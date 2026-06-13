mdmagma
=======

Magma code for computing with modular curves by Maarten Derickx and Andrew V. Sutherland.

# Installation

Clone the repository with submodules initialised:

```shell
git clone --recurse-submodules https://github.com/nt-lib/mdmagma.git
```

If you already cloned without `--recurse-submodules`, initialise them afterwards:

```shell
git submodule update --init
```

# Requirements

This requires [Andrew V. Sutherlands magma package](https://github.com/AndrewVSutherland/Magma). It is known to work with the version [commit 6a5a68a8c5ba...](https://github.com/AndrewVSutherland/Magma/tree/6a5a68a8c5ba526b707f746d559c8f23cbe641b1), and should also work with later versions.

# Research Papers

The code in this project has been used for the following research papers:

[Gonality of the modular curve X<sub>1</sub>(N)](https://arxiv.org/abs/1307.5719)

[Torsion subgroups of elliptic curves over quintic and sextic number fields](http://arxiv.org/abs/1608.07549)


# Version 2

A version 2 that is more consistent and organized is under development. 
V2 will use intrinsics, user defined types and have automated tests.
This is currently done in the v2 subfolder.

## Using V2

To use V2 run 

```shell
cd v2
magma
```

And then from withing magma run

```magma
AttachSpec("mdmagma.spec");
```

### Dependencies

mdmagma depends on https://github.com/AndrewVSutherland/Magma .
Note that `AttachSpec("mdmagma.spec");` also makes sure that all external dependencies
are attached. If you want to attach the files from mdmagma without also attaching the
dependencies then you need to attach `mdmagma_internal.spec` instead. This is usefull if
you already have the dependencies of mdmagma attached by default or if you are using 
[CHIMP](https://github.com/edgarcosta/CHIMP/). There is no guarantee that mdmagma will
work with dependencies other than those listed by running:

```bash
git submodule
```




## Testing

If you have Magma installed locally:

```shell
make test
```

If you do not have Magma installed locally but have SSH access to a machine that does,
you can run the tests remotely. The makefile will rsync the repository to `/tmp/mdmagma`
on the remote host and run the tests there:

```shell
make test_remote ssh=<hostname>
```

For manual invocation without make, note that the tests must be run from the `tests/`
directory:

```shell
cd tests
magma -n v2/test_all.m
```

# Troubleshooting

## "Can't open package spec file ... Magma/magma.spec"

This error occurs during regular usage and tests. The `Magma/` directory is a git submodule that must be initialised:

```shell
git submodule update --init
```

# Copyright

    copyright (C) 2025 Maarten Derickx, Andrew Sutherland
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with this program.  If not, see [http://www.gnu.org/licenses/].
