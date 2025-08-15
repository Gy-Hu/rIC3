FROM messense/rust-musl-cross:x86_64-musl AS builder

WORKDIR /work
COPY . .
RUN git submodule update --init

# 清理符号链接冲突
RUN find . -name "makefile" -type l -delete || true
RUN find . -name "Makefile" -type l -delete || true

# 添加 musl 目标并构建静态二进制
RUN rustup target add x86_64-unknown-linux-musl
RUN cargo build --release --target x86_64-unknown-linux-musl

FROM scratch
COPY --from=builder /work/target/x86_64-unknown-linux-musl/release/rIC3 /usr/local/bin/rIC3
ENTRYPOINT ["/usr/local/bin/rIC3"]
