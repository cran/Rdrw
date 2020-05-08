\docType{package}
\name{Rdrw}
\alias{Rdrw-package}
\title{Univariate and Multivariate Damped Random Walk Processes}
\description{
The R package \pkg{Rdrw} provides a toolbox to fit and simulate univariate and multivariate damped random walk processes, possibly with known measurement error standard deviations via state-space representation. The damped random walk process is also known as an Ornstein-Uhlenbeck process or a continuous-time auto-regressive model with order one, i.e., CAR(1) or CARMA(1, 0). The package \pkg{Rdrw} adopts Kalman-filtering to evaluate the resulting likelihood function of the model parameters, leading to a linear complexity in the number of unique observation times. The package provides two functionalities; (i) it fits the model and returns the maximum likelihood estimates or posterior samples of the model parameters; (ii) it simulates time series data following the univariate or multivariate damped random walk process.
}
\details{
\tabular{ll}{
Package: \tab Rdrw\cr
Type: \tab Package\cr
Version: \tab 1.0.0\cr
Date: \tab 2020-5-6\cr
License: \tab GPL-2\cr
Main functions: \tab \code{\link{drw}}, \code{\link{drw.sim}}\cr
}
}
\author{
Zhirui Hu and Hyungsuk Tak
}