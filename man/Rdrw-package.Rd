\docType{package}
\name{Rdrw}
\alias{Rdrw-package}
\title{Univariate and Multivariate Damped Random Walk Processes}
\description{
The \pkg{Rdrw} package provides tools for fitting and simulating univariate and multivariate damped random walk processes with optional measurement error standard deviations in a state-space framework. The damped random walk process is also known as an Ornstein--Uhlenbeck process or a first-order continuous-time autoregressive model, CAR(1) or CARMA(1, 0). The package uses Kalman filtering to evaluate the likelihood efficiently, with linear complexity in the number of unique observation times. Polynomial mean coefficients are handled conditionally within the Kalman recursion: they are profiled by generalized least squares for maximum likelihood estimation and sampled from their exact Gaussian conditional distribution for Bayesian inference. The main function \code{\link{drw}} fits the model and returns maximum likelihood estimates or posterior samples of the model parameters. The function \code{\link{drw.sim}} simulates time series from univariate or multivariate damped random walk processes.
}
\details{
\tabular{ll}{
Package: \tab Rdrw\cr
Type: \tab Package\cr
Version: \tab 1.0.4\cr
Date: \tab 2026-08-10\cr
License: \tab GPL-2\cr
Main functions: \tab \code{\link{drw}}, \code{\link{drw.sim}}\cr
}
}
\author{
Zhirui Hu and Hyungsuk Tak
}
\references{
Zhirui Hu and Hyungsuk Tak (2020), "Modeling Stochastic Variability in Multi-Band Time Series Data," doi:10.3847/1538-3881/abc1e2.
}
