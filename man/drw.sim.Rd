\name{drw.sim}
\alias{drw.sim}
\title{Simulating Univariate and Multivariate Damped Random Walk Processes}
\usage{
drw.sim(time, n.datasets, measure.error.SD, mu, sigma, tau, rho)
}
\arguments{
\item{time}{A vector of observation times. Let n denote the length of this vector.}
\item{n.datasets}{A positive integer giving the number of time series to be simulated. In simulation, there is no upper limit on the number of time series. Let k denote this number.}
\item{measure.error.SD}{Optional measurement error standard deviations. If one time series is simulated, this is a vector of length n. If more than one time series is simulated, this is an n by k matrix of measurement error standard deviations. If this information is unavailable, it is automatically set to zero.}
\item{mu}{A vector of length k containing the long-term mean parameter or parameters.}
\item{sigma}{A vector of length k containing the short-term variability parameter or parameters, expressed as standard deviations.}
\item{tau}{A vector of length k containing the timescale parameter or parameters.}
\item{rho}{Required when more than one time series is simulated, k > 1. This is a vector of length k(k - 1) / 2 containing the cross-correlation parameters. For example, if k = 3, this vector contains rho_12, rho_13, and rho_23. If k = 5, this vector contains rho_12, rho_13, rho_14, rho_15, rho_23, rho_24, rho_25, rho_34, rho_35, and rho_45.}
}
\value{
The output of \code{drw.sim} is a list containing:
\describe{
\item{x}{An n by k matrix of simulated time series. Each column corresponds to one simulated time series.}
}
}
\description{
The function \code{drw.sim} simulates one or more time series from univariate or multivariate damped random walk processes.
}
\details{
Given observation times and model parameter values \code{mu}, \code{sigma}, \code{tau}, and optionally \code{rho}, this function simulates k time series, optionally including known measurement error standard deviations.
}
\examples{
########## Simulating a multivariate damped random walk process

n <- 100
k <- 5
obs.time <- cumsum(rgamma(n, shape = 3, rate = 1))

tau <- 100 + 20 * (1:5)
sigma <- 0.01 * (1:5)
mu <- 17 + 0.5 * (1:5)

rho.m <- matrix(0, k, k)
for (i in 1:k) {
  for (j in 1:k) {
    rho.m[i, j] <- 1.1^(-abs(i - j))
  }
}

rho <- rho.m[upper.tri(rho.m)]

measure.error.band <- c(0.010, 0.014, 0.018, 0.022, 0.026)
measure.error <- NULL
for (i in 1:k) {
  measure.error <- cbind(measure.error, rnorm(n, measure.error.band[i], 0.002))
}

x <- drw.sim(time = obs.time, n.datasets = 5, measure.error.SD = measure.error,
             mu = mu, sigma = sigma, tau = tau, rho = rho)

plot(obs.time, x[, 1], xlim = c(min(obs.time), max(obs.time)), ylim = c(17, 20),
     xlab = "time", ylab = "observation")
points(obs.time, x[, 2], col = 2, pch = 2)
points(obs.time, x[, 3], col = 3, pch = 3)
points(obs.time, x[, 4], col = 4, pch = 4)
points(obs.time, x[, 5], col = 5, pch = 5)

########## Simulating a univariate damped random walk process

x <- drw.sim(time = obs.time, n.datasets = 1, measure.error.SD = measure.error[, 1],
             mu = mu[1], sigma = sigma[1], tau = tau[1])
plot(obs.time, x)
}
\author{
Zhirui Hu and Hyungsuk Tak
}
\references{
Zhirui Hu and Hyungsuk Tak (2020), "Modeling Stochastic Variability in Multi-Band Time Series Data," doi:10.48550/arXiv.2005.08049.
}
