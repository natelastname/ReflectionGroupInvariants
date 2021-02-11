
# Introduction

This project is a boilerplate example of how to use SageMath to calculate the action of a finite matrix group on its ring of coinvariants using SageMath. 

For example, this project shows how to construct the regular representation of a finite matrix group G from the action of G on its ring of coinvariants (See Proposition 4.9 of [this paper by Richard P. Stanley.](http://www-math.mit.edu/~rstan/pubs/pubfiles/38.pdf))

SageMath is theoretically capable of performing these types of computations using nothing but the SageMath standard library. This is infact true, but there are a few bugs that one is likely to encounter while writing an implementation that require a lot of debugging to overcome. The comments in the source explain what these bugs are and how to work around them.

## Usage

To run the default examples, open Sage and run the following command:

`sage: load("main.sage.py")`


## Dependencies

Requires the GAP3 package *Chevie*. See [here](https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/root_system/reflection_group_complex.html) for installation instructions.

**Note:** On my machine, running the command `$ sage -i gap3` as the SageMath documentation suggests did not work. Instead, I had to download `gap3-jm` from [here](https://webusers.imj-prg.fr/~jean.michel/gap3/) and install it by dropping a binary in my `/usr/bin` (among other things.) This is not an elegant process, but if you know what you are doing and follow the directions it will work. 

To check if chevie is set up correctly or if you already have Chevie installed, run the following commands:

    $ gap3
    gap> LoadPackage("chevie");

If these do not produce errors, Chevie is working. 











