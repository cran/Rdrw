\name{drw.sim}
\alias{drw.sim}
\title{Simulating univariate and multiviarate damped random walk processes}
\usage{
drw.sim(time, n.datasets, measure.error.SD, mu, sigma, tau, rho)
}
\arguments{
\item{time}{A vector containing observation times. Let us use \eqn{n} to denote the length of this vector.
}
\item{n.datasets}{Any positive integer value that denotes the number of time series data sets to be simulated. In simulation, there is no upper limit in the number of time series data sets. Let's use \eqn{k} to denote this number of time series data sets.
}
\item{measure.error.SD}{Optional if measurement error standard deviations are known and available. If one time series data set is simulated, it is a vector of length \eqn{n} containing measurement error standard deviations. If more than one time series data sets are simulated, it is an \eqn{n} by \eqn{k} matrix composed of measurement error standard deviations. If such information is not available, it is automatically set to zeros.}

\item{mu}{A vector of length \eqn{k}, containing the long-term average parameter(s) of the process.}

\item{sigma}{A vector of length \eqn{k}, containing the short-term variability parameter(s) (standard deviation) of the process.}

\item{tau}{A vector of length \eqn{k}, containing the timescale parameter(s) of the process.}

\item{rho}{Required if more than one time series data sets are simulated \eqn{(k>1)}. A vector of length \eqn{k(k-1)/2}, containing the cross-correlation parameters of the process. For example, if \eqn{k=3}, this is a vector composed of \eqn{\rho_{12}}, \eqn{\rho_{13}}, \eqn{\rho_{23}}. If \eqn{k=5}, this is a vector composed of \eqn{\rho_{12}}, \eqn{\rho_{13}}, \eqn{\rho_{14}}, \eqn{\rho_{15}}, \eqn{\rho_{23}}, \eqn{\rho_{24}}, \eqn{\rho_{25}}, \eqn{\rho_{34}}, \eqn{\rho_{35}}, \eqn{\rho_{45}}.}
}
\value{
The outcome of \code{drw.sim} is composed of:
\describe{
\item{x}{An \eqn{n} by \eqn{k} matrix composed of \eqn{k} simulated time series data each with length \eqn{n}. That is, each column is corresponding to one simulated time series data set.}
}
}
\description{
The function \code{drw.sim} simulates time series data set(s) following either univariate or multivariate damped random walk process.
}
\details{
Given the \eqn{n} observation times and model parameter values (mu, sigma, tau, rho) possibly with known measurement error standard deviations, this function simulates \eqn{k} time series data sets.
}
\examples{
########## Simulating a multivariate damped random walk process

n <- 100
k <- 5
obs.time <- cumsum(rgamma(n, shape = 3, rate = 1))

tau <- 100 + 20 * (1 : 5) #rnorm(k, 0, 5)
sigma <- 0.01 * (1 : 5)
#tau <- c(1 : 5) #rnorm(k, 0, 5)
#sigma <- 0.05  + 0.007 * (0 : 4) #rnorm(k, 0, 0.002)
mu <- 17 + 0.5 * (1 : 5)

rho.m <- matrix(0, k, k)
for(i in 1 : k) {
  for(j in 1 : k) {
    rho.m[i, j] = 1.1^(-abs(i - j))
  }
}

rho <- rho.m[upper.tri(rho.m)]

measure.error.band <- c(0.010, 0.014, 0.018, 0.022, 0.026)
measure.error <- NULL
for(i in 1 : k) {
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
