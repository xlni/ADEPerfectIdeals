-*
to obtain random homogeneous specializations, we pick a homomorphism
Z^n -> Z (where Z^n is the root lattice).
Note that with the way things have been set up, the variables in the generic examples have
negative multidegrees.
*-

--in order to make this a local homomorphism we don't want to send any variables to constants:
nonconstrandom = (n,R) -> if n > 0 then return random(n,R) else return 0_R;

--Here is an example for E_6.

(c,d,t) = (3,2,2);load "preparation.m2"
lambda = matrix{{0,0,-1,0,0,1}}; sigmaraw = {3,4,2,5,4,3,1,3,4,2,5,4,6,5,3,4,2};
load "computation.m2"

--ring in which to produce the example
S = ZZ/32003[X,Y,Z]

--example homomorphism Z^n -> Z
--this one causes F_1 and F_3 to each be generated in a single degree
degspec = (-1)*matrix{{0,0,1,0,0,0}}

--the random specialization using the above degree homomorphism
randomspec = apply(gens Rs, i -> i => nonconstrandom((degspec*(transpose matrix {degree i}))_(0,0),S));

--apply it to F:
ranF = chainComplex(
    rand1 = map(S^1,,sub(F.dd_1,randomspec)),
    rand2 = map(source rand1,,sub(F.dd_2,randomspec)),
    rand3 = map(source rand2,,sub(F.dd_3,randomspec))
    )

--the homomorphism might have lowered the codimension of the ideal!
--to check that this didn't happen, we see if the specialized complex is still acyclic:
prune HH ranF
betti ranF

--another example, this time using a grading that causes F_2 to be generated in a single degree:
sw = symbol sw;sa = symbol sa;n=6;
for i from 1 to n do (
    	sw_i = id_(ZZ^n)-(map(ZZ^n,ZZ^(i-1),0)|g.cache#"CM"_{i-1}|map(ZZ^n,ZZ^(n-i),0));
	sa_i = transpose sw_i --this is just transpose sw_i
    )
sigma = lift(product(apply(sigmaraw, i -> sa_i)),ZZ)

degspec = matrix{{0,1,0,0,0,0}}*(inverse sigma)

ranF = chainComplex(
    rand1 = map(S^1,,sub(F.dd_1,randomspec)),
    rand2 = map(source rand1,,sub(F.dd_2,randomspec)),
    rand3 = map(source rand2,,sub(F.dd_3,randomspec))
    )
prune HH ranF
betti ranF

