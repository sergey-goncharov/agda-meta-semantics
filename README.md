# agda-meta-semantics
Categorical semantic toolset in Agda

The idea of this repository is to collect categorical tools for semantics, and for mechanized reasoning about semantics. 

The underlying notion of category is chosen to be the one, implemented in the [agda-categories](https://github.com/agda/agda-categories) library. 

A primary focus at the moment is formalization of the concepts and results of the __Higher-Order Mathematical Operational Semantics__ program, started in the paper: https://dl.acm.org/doi/10.1145/3571215

## Requirements
This project assumes the most recent version of agda-categories (i.e. the upstream main branch), which depends on version 2.0 of agda-stdlib and Agda-2.6.4.

We have supplied a `flake.nix` which provides a suitable environment for running this project.

The environment can be entered via
```sh
nix develop .
```
or 
```sh
direnv allow
```
when using [direnv](https://github.com/direnv/direnv)

## Usage
To typecheck the project, run
```sh
make agda
```

To generate clickable HTML files, run
```sh
make html
```

then open `meta-semantics/index.html` (`make open`).

A somewhat recent version of the HTML output is also hosted on [https://wwwcip.cs.fau.de/~hy84coky/meta-semantics/](https://wwwcip.cs.fau.de/~hy84coky/meta-semantics/).