use std::{
    fmt::{self, Debug},
    ops::{Add, AddAssign},
    time::{Duration, Instant},
};

#[derive(Default, Clone, Copy)]
pub struct Average {
    sum: f64,
    num: usize,
}

impl Debug for Average {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.6}", self.sum / self.num as f64)
    }
}

impl AddAssign<usize> for Average {
    fn add_assign(&mut self, rhs: usize) {
        self.sum += rhs as f64;
        self.num += 1;
    }
}

impl AddAssign<f64> for Average {
    fn add_assign(&mut self, rhs: f64) {
        self.sum += rhs;
        self.num += 1;
    }
}

impl Add<Average> for Average {
    type Output = Self;

    fn add(self, rhs: Average) -> Self::Output {
        Self {
            sum: self.sum + rhs.sum,
            num: self.num + rhs.num,
        }
    }
}

impl AddAssign<Average> for Average {
    #[inline]
    fn add_assign(&mut self, rhs: Average) {
        self.sum += rhs.sum;
        self.num += rhs.num;
    }
}

#[derive(Default, Clone, Copy)]
pub struct AverageDuration {
    sum: Duration,
    num: usize,
}

impl Debug for AverageDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.num == 0 {
            write!(f, "None")
        } else {
            write!(f, "{:?}", self.sum / self.num as u32)
        }
    }
}

impl AddAssign<Duration> for AverageDuration {
    fn add_assign(&mut self, rhs: Duration) {
        self.sum += rhs;
        self.num += 1;
    }
}

#[derive(Default, Clone, Copy)]
pub struct SuccessRate {
    succ: usize,
    fail: usize,
}

impl SuccessRate {
    pub fn success(&mut self) {
        self.succ += 1;
    }

    pub fn fail(&mut self) {
        self.fail += 1;
    }

    pub fn statistic(&mut self, success: bool) {
        if success { self.success() } else { self.fail() }
    }
}

impl Add for SuccessRate {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            succ: self.succ + rhs.succ,
            fail: self.fail + rhs.fail,
        }
    }
}

impl AddAssign for SuccessRate {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.succ += rhs.succ;
        self.fail += rhs.fail;
    }
}

impl Debug for SuccessRate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "success: {}, fail: {}, success rate: {:.2}%",
            self.succ,
            self.fail,
            (self.succ as f64 / (self.succ + self.fail) as f64) * 100_f64
        )
    }
}

#[derive(Default)]
pub struct Case(String);

impl Case {
    pub fn new<S: ToString>(s: S) -> Self {
        Self(s.to_string())
    }
}

impl Debug for Case {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct RunningTime {
    start: Instant,
}

impl RunningTime {
    #[inline]
    pub fn start(&self) -> Duration {
        self.start.elapsed()
    }

    #[inline]
    pub fn stop(&self, start: Duration) -> Duration {
        self.start.elapsed() - start
    }
}

impl Default for RunningTime {
    fn default() -> Self {
        Self {
            start: Instant::now(),
        }
    }
}

impl Debug for RunningTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.2}s", self.start.elapsed().as_secs_f64())
    }
}
