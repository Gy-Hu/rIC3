# rIC3-static

A static-compiled hardware model checker with witness dumping functionality.

## Features

- ✅ Hardware model checking with IC3/PDR algorithm
- ✅ **Dump witness functionality** - Generate and save counterexample witnesses
- ✅ **Static musl compilation** - Runs on any Linux x86_64 without dependencies
- ✅ **Certifaiger integration** - Generated witnesses are verifiable
- ✅ Multiple engines: IC3, BMC, K-induction, Portfolio
- ✅ Docker support with minimal scratch-based images

## Quick Start

### Using Pre-built Static Binary

If you have the static binary `rIC3-musl-static`:

```bash
# Run model checking with witness dumping
./rIC3-musl-static examples/counter/counter.aig --dump-witness witness.aiw --engine ic3

# Verify the witness with certifaiger
docker run --rm -v $(pwd):/data ghcr.io/gipsyh/certifaiger /data/counter.aig /data/witness.aiw
```

### Using Docker

```bash
# Build the minimal Docker image
docker build -f Dockerfile.final -t ric3-static .

# Run with volume mount for input/output files
docker run --rm -v $(pwd)/examples/counter:/data ric3-static \
  /data/counter.aig --dump-witness /data/witness.aiw --engine ic3
```

## Building from Source

### Prerequisites

#### For macOS:
```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install musl cross-compilation tools
brew install musl-cross

# Add musl target
rustup target add x86_64-unknown-linux-musl
```

#### For Linux:
```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install musl tools (Ubuntu/Debian)
sudo apt-get install musl-tools musl-dev

# Add musl target
rustup target add x86_64-unknown-linux-musl
```

### Build Steps

1. **Clone and setup**:
```bash
git clone <repository-url>
cd rIC3-static
```

2. **Configure for musl compilation**:
```bash
# The project is already configured with:
# - .cargo/config.toml for musl linker
# - Cargo.toml with vendored-openssl feature
```

3. **Build static binary**:
```bash
# This will take 5-10 minutes due to compiling OpenSSL from source
cargo build --target x86_64-unknown-linux-musl --release
```

4. **Verify the binary**:
```bash
file target/x86_64-unknown-linux-musl/release/rIC3
# Should output: ELF 64-bit LSB pie executable, x86-64, version 1 (SYSV), static-pie linked, stripped
```

### Build Docker Image

```bash
# Copy binary to avoid .dockerignore issues
cp target/x86_64-unknown-linux-musl/release/rIC3 ./rIC3-musl-static

# Build minimal Docker image (scratch-based, ~1.8MB)
docker build -f Dockerfile.final -t ric3-static .
```

## Usage

### Command Line Options

```bash
rIC3 [OPTIONS] <MODEL> [CERTIFICATE]

Key Options:
  --dump-witness <FILE>     Dump witness to file when model is unsafe
  --witness                 Print witness to stdout when model is unsafe
  --engine <ENGINE>         Choose engine: ic3, bmc, kind, portfolio
  --certify                 Verify certificate with certifaiger
  -v <LEVEL>               Verbose level (0-3)
```

### Examples

#### Basic Model Checking
```bash
# Check if model is safe
./rIC3 examples/counter/counter.aig --engine ic3

# Check with witness dumping
./rIC3 examples/counter/counter.aig --dump-witness counter_witness.aiw --engine ic3
```

#### Using Different Engines
```bash
# Use BMC (Bounded Model Checking)
./rIC3 model.aig --engine bmc --bmc-max-k 50

# Use K-induction
./rIC3 model.aig --engine kind

# Use portfolio (default - tries multiple engines)
./rIC3 model.aig --engine portfolio
```

#### Witness Verification
```bash
# Generate witness
./rIC3 examples/counter/counter.aig --dump-witness witness.aiw --engine ic3

# Verify with certifaiger
docker run --rm \
  -v $(pwd)/examples/counter/counter.aig:/model.aig \
  -v $(pwd)/witness.aiw:/witness.aiw \
  ghcr.io/gipsyh/certifaiger /model.aig /witness.aiw
```

## Input Formats

- **AIGER (.aig)**: Binary format for And-Inverter Graphs
- **BTOR2 (.btor, .btor2)**: Word-level format for hardware verification

## Output Formats

### Results
- `safe`: No counterexample found within bounds
- `unsafe`: Counterexample found (witness available)
- `unknown`: Solver timeout or resource limits

### Witness Format
Generated witnesses follow the AIGER witness format:
```
1
b0
0000000000  # Initial state
00          # Input at step 0
00          # Input at step 1
...
.
```

## Development

### Key Changes Made

This version includes several important fixes and enhancements:

1. **Fixed AIG Processing Bug**:
   - Resolved variable confusion in `AigFrontend::new()`
   - Fixed preprocessing pipeline that was removing properties
   - Added fallback for when `aig_preprocess` removes properties

2. **Added Dump Witness Feature**:
   - New `--dump-witness` command line option
   - Integrated witness generation into certificate processing
   - Full compatibility with certifaiger verification

3. **Enabled musl Static Compilation**:
   - Configured git2 to use `vendored-openssl`
   - Set up cross-compilation toolchain
   - Created minimal Docker images

### Project Structure
```
rIC3-static/
├── src/
│   ├── frontend/aig/
│   │   ├── mod.rs           # AIG processing (FIXED)
│   │   └── certificate.rs   # Witness generation (ENHANCED)
│   ├── options.rs          # Command line options (ADDED --dump-witness)
│   └── ...
├── deps/
│   ├── giputils/           # Modified to use vendored-openssl
│   ├── aig-rs/
│   ├── logic-form/
│   └── satif/
├── examples/counter/       # Test case
├── .cargo/config.toml     # musl linker configuration
└── Dockerfile.final       # Minimal Docker image
```

### Testing

```bash
# Run basic test
cargo test

# Test static binary
./target/x86_64-unknown-linux-musl/release/rIC3 examples/counter/counter.aig --engine ic3

# Test witness generation and verification
./target/x86_64-unknown-linux-musl/release/rIC3 examples/counter/counter.aig \
  --dump-witness test_witness.aiw --engine ic3
docker run --rm -v $(pwd):/data ghcr.io/gipsyh/certifaiger \
  /data/examples/counter/counter.aig /data/test_witness.aiw
```

## Troubleshooting

### Build Issues

**OpenSSL compilation errors**:
- Ensure musl-tools are installed
- Check that `vendored-openssl` feature is enabled in `deps/giputils/Cargo.toml`
- Use longer timeout: `cargo build --target x86_64-unknown-linux-musl --release` (takes 5-10 minutes)

**Cross-compilation errors**:
- Verify `.cargo/config.toml` has correct linker: `x86_64-linux-musl-gcc`
- Check musl target is installed: `rustup target list --installed`

### Runtime Issues

**"AIG preprocessing removed the property" warning**:
- This is expected for some models and is automatically handled
- The tool falls back to unprocessed model to avoid crashes

**Empty witness files**:
- Check that model is actually unsafe (result should be "unsafe")
- Verify `--dump-witness` path is writable

## Complete Build Flow

Here's the complete step-by-step process from zero to working static binary:

### 1. Initial Setup (One-time)
```bash
# Install Rust if not already installed
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env

# Install musl cross-compilation tools
# On macOS:
brew install musl-cross
# On Linux (Ubuntu/Debian):
sudo apt-get install musl-tools musl-dev

# Add musl target
rustup target add x86_64-unknown-linux-musl
```

### 2. Configure Project for Static Compilation
```bash
# Clone the repository
git clone <your-repo-url>
cd rIC3-static

# The following files should already be configured:

# .cargo/config.toml
echo '[target.x86_64-unknown-linux-musl]
linker = "x86_64-linux-musl-gcc"' > .cargo/config.toml

# deps/giputils/Cargo.toml should have:
# git2 = { version = "0.20.0", features = ["vendored-openssl"] }
```

### 3. Build Process
```bash
# Build static binary (takes 5-10 minutes due to OpenSSL compilation)
cargo build --target x86_64-unknown-linux-musl --release

# Verify the binary is truly static
file target/x86_64-unknown-linux-musl/release/rIC3
# Expected: ELF 64-bit LSB pie executable, x86-64, version 1 (SYSV), static-pie linked, stripped

# Test the binary
./target/x86_64-unknown-linux-musl/release/rIC3 --help
```

### 4. Docker Packaging
```bash
# Copy binary to avoid .dockerignore
cp target/x86_64-unknown-linux-musl/release/rIC3 ./rIC3-musl-static

# Create minimal Dockerfile.final:
echo 'FROM scratch
COPY ./rIC3-musl-static /rIC3
ENTRYPOINT ["/rIC3"]' > Dockerfile.final

# Build minimal Docker image
docker build -f Dockerfile.final -t ric3-static .

# Test Docker image
docker run --rm ric3-static --help
```

### 5. End-to-End Testing
```bash
# Test with example file
./target/x86_64-unknown-linux-musl/release/rIC3 \
  examples/counter/counter.aig \
  --dump-witness witness.aiw \
  --engine ic3

# Verify witness with certifaiger
docker run --rm \
  -v $(pwd)/examples/counter/counter.aig:/model.aig \
  -v $(pwd)/witness.aiw:/witness.aiw \
  ghcr.io/gipsyh/certifaiger /model.aig /witness.aiw
```

### Expected Output
```
# Model checking result:
result: unsafe

# Certifaiger verification:
check: unsafe
check_sat: simulating trace /witness.aiw
check_sat: Trace simulation passed
check: valid witness
```

## License

GPL-3.0

## Authors

- Original rIC3: Yuheng Su <gipsyh.icu@gmail.com>
- Static compilation & witness features: Enhanced with Claude Code assistance

## Contributing

1. Fork the repository
2. Create feature branch
3. Test with both native and musl builds
4. Verify witness generation works
5. Submit pull request

---

**Note**: This static-compiled version ensures maximum portability and includes enhanced witness generation capabilities verified against the certifaiger standard.