# ADEPerfectIdeals
Macaulay2 code for producing examples of perfect ideals using representation theory.

## Brief background
Consider a T-shaped graph `T` with left arm of length `c-2`, right arm of length `d`, and bottom arm of length `t` where `c >= 2`, `d >= 0`, and `t >= 1` are integers. This graph is a Dynkin diagram exactly when
```
1/(c-1) + 1/(d+1) + 1/(t+1) > 1.
```
We henceforth assume this to be the case. In this setting, let `G` be the associated simply connected complex Lie group, and `P` the maximal parabolic corresponding to the diagram obtained by deleting the left-most vertex from `T`. Inside of the homogeneous space `G/P`, there are two linked Schubert varieties of codimension `c`, in the sense that their union is cut out by a regular sequence of length `c`.

The purpose of this code is to produce the defining ideals of these Schubert varieties when restricted to certain cells. Each of these is a homogeneous ideal in a multigraded polynomial ring.

The interest in these examples is because they conjecturally give the generic examples of perfect ideals of grade `c`, deviation at most `d`, and type at most `t`. This is classically known for `c = 2` and it is proven for `c = 3` (over a field of characteristic zero) in [this preprint](https://math.berkeley.edu/~xlni/Preprints/ADE.pdf).
## Usage
### Generic examples
To see the generic examples, i.e. the defining ideals of particular Schubert varieties, load the file `Demo.m2`. Find the example of interest, evaluate the line that looks like
```
(c,d,t) = ...; load "preparation.m2"
```
and then the line
```
lambda = ..., sigmaraw = ...
```
corresponding to the cell of interest. Finally, evaluate the line
```
load "computation.m2"
```
Depending on the values of `c,d,t`, this computes either the resolution `F` or some part of it. The part computed is written on the next line, e.g. if the next line is
```
d3;d2;
```
that means the differentials `d3` and `d2` were computed, but not the rest of the resolution.
### Random specializations
There is also a file `SpecializationDemo.m2` that shows how one can produce random homogeneous examples in a standard graded polynomial ring by choosing a homomorphism from the root lattice to the integers; you can try sequentially evaluating all the commands in that file.
### Other Schubert varieties
The very particular Schubert varieties were the main motivation for writing this code, but this code is actually capable of computing the defining ideals of *any* Schubert variety in `G/P` provided that the user can provide the irreducible representation inside of which to embed `G/P` via the Plucker embedding. The file `SchubertDemo.m2` shows how to do this. 
## Other comments
The very particular Schubert varieties were the main motivation for writing this code, but this code is actually capable of computing the defining ideals of *any* Schubert variety in `G/P` for the maximal parabolics `P_1,P_2,P_6` for `E_6`, the maximal parabolics `P_1,P_2,P_7` for `E_7`, and the maximal parabolic `P_8` for `E_8`. (This is simply because the associated fundamental representations are the ones which I managed to implement in M2 by very ad-hoc methods. It is hopeless to explicitly implement the other two extremal fundamental representations for `E_8`.)