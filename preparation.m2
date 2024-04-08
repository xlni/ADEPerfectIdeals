needsPackage "DynkinPerfectIdeals"

--methods that should be put into main package

--gets the eigenspace in V for action of h_n with eigenvalue k
gradedComponent = method();
gradedComponent(LieAlgebraRep,ZZ,Thing) := Matrix => (V,n,k) -> (
    g := algebra V;
    return gens trim ker ((action V)*(g.cache#"h"_{n-1}**id_(module V))-k);
    )

genericMultigradePos = method();
genericMultigradePos (LieAlgebra) := Matrix => (g) -> (
    if g.cache#?"positiveparametrization" then return g.cache#"positiveparametrization";
    x := symbol x;
    kk := ring module g;
    n := numcols g.cache#"e";
    grd := apply(n, i -> (bracket g)*(g.cache#"h"_{i}**id_(module g)));
    degmax := apply(n, i -> (
	    j := 0;
    	    while not zero ker (grd#i+j) do j = j+1;
    	    return j
	    )
	);
    hgrade := hashTable {{}=>module g};
    for i from 0 to n-1 do (
    	newhgrade := new MutableHashTable;
    	for k in keys hgrade do (
    	    jmin := -degmax_i; --if member(i,{2,3}) then jmin := 1 else jmin = 0;
	    for j from -degmax_i to 0 do (
	    	temp := intersect (hgrade#k, ker (grd#i+j));
	    	if not zero temp then newhgrade#(k|{j}) = temp
    	    	);
	    );
    	hgrade = new HashTable from newhgrade
	);
    hgrade = applyPairs(hgrade, (k,v) -> if not all(k,zero) then (k,v)); --remove the part for the Cartan
    numvars := applyValues(hgrade, v -> numcols gens v);
    varl := transpose flatten apply(pairs hgrade,
	(k,v) -> apply(toList(1..(numcols gens v)), i -> {k,x_((toSequence (-k))|(1:i))})
	);
    R := kk[varl_1, Degrees => varl_0];
    varHT := applyPairs(hgrade,
	(k,v) -> (k,apply(toList(1..(numcols gens v)),i -> (x_((toSequence (-k))|(1:i)))_R))
	);
    g.cache#"parametersymbol" = x;
    return g.cache#"positiveparametrization" = sum(keys hgrade, k -> (gens hgrade#k)*(transpose matrix{toList varHT#k}))
    )

--just for converting lists {a,b,c} to numbers abc for aesthetic purposes
--assumes that the numbers in the list are between 1 and 9
seqToNum = method();
seqToNum(List) := ZZ => l -> (
    n := length l;
    return sum(n, i -> 10^(n-i-1)*l_i)
    )

antiDiagonalMatrix = method();
antiDiagonalMatrix(ZZ) := Matrix => N -> (
    map(ZZ^N,ZZ^N,apply(N, i -> (N-i-1,i) => 1))
    )

simpleRefAction = method();
simpleRefAction(ZZ,LieAlgebraRep) := Matrix => (j,V) -> (
    if V.cache#?"simplerefs" then return V.cache#"simplerefs"#j;
    g := algebra V; n := numrows g.cache#"CM";
    V.cache#"simplerefs" = new MutableHashTable;
    for j from 1 to n do (
	V.cache#"simplerefs"#j = (
	    (exp parametricAction(V,g.cache#"f"_{j-1}))
	    *(exp parametricAction(V,(-1)*g.cache#"e"_{j-1}))
	    *(exp parametricAction(V,g.cache#"f"_{j-1}))
	    )
    	);
    return V.cache#"simplerefs"#j
    )
simpleRefAction(List,LieAlgebraRep) := Matrix => (l,V) -> (
    product(apply(l,j->simpleRefAction(j,V))|{id_(module V)})
    )

--max eigenvalue for action of h_j on V
maxEigenvalue = method();
maxEigenvalue(LieAlgebraRep,ZZ) := QQ => (V,j) -> (
    g := algebra V;
    v := invariants(g.cache#"e",V);
    return (((action V)*(g.cache#"h"_{j-1}**v))//v)_(0,0)
    )
--parameters c,d,t
excludeddiffs = {};
if c == 3 then (
    if (d,t) == (2,2) and not (E6swap===true) then (
	g = lieAlgebra("E",6);
	ndiagram = {6,5,4,2};
	tdiagram = {1};
	f2diagram = {6,5,4,3,1};
	rednode = 3;
	Lreps = {
    	    ({1,1},{1}),
    	    ({1,1,1,1},{1,1})
    	    };
	) else
    if (d,t) == (2,2) and (E6swap===true) then (
	g = lieAlgebra("E",6);
	ndiagram = {1,3,4,2};
	tdiagram = {6};
	f2diagram = {1,3,4,5,6};
	rednode = 5;
	Lreps = {
    	    ({1,1},{1}),
    	    ({1,1,1,1},{1,1})
    	    };
	) else
    if member((d,t),{(2,3),(3,2)}) then (
	g = lieAlgebra("E",7);
	if (d,t) == (2,3) then (
	    ndiagram = {1,3,4,2};
	    tdiagram = {6,7};
	    f2diagram = {1,3,4,5,6,7};
	    rednode = 5;
	    Lreps = {
    	    	({1,1},{1}),
    	    	({1,1,1,1},{1,1}),
		({2,1,1,1,1},{1,1,1})
    	    	};	
	    ) else
	if (d,t) == (3,2) then (
	    ndiagram = {7,6,5,4,2};
	    tdiagram = {1};
	    f2diagram = {7,6,5,4,3,1};
	    rednode = 3;
	    Lreps = {
    	    	({1,1},{1}),
    	    	({1,1,1,1},{1,1}),
		({1,1,1,1,1,1},{2,1})
    	    	};
	    )
	) else
    if member((d,t),{(2,4),(4,2)}) then (
	g = lieAlgebra("E",8);
	if (d,t) == (2,4) then (
	    excludeddiffs = {1,2};
	    ndiagram = {1,3,4,2};
	    tdiagram = {6,7,8};
	    f2diagram = {1,3,4,5,6,7,8};
	    rednode = 5;
	    Lreps = {
    	    	({1,1},{1}),
    	    	({1,1,1,1},{1,1}),
		({2,1,1,1,1},{1,1,1}),
		({2,2,2,1,1},{1,1,1,1}),
		({2,2,2,2,2},{2,1,1,1})
    	    	};
	    ) else
	if (d,t) == (4,2) then (
	    excludeddiffs = {1,3};
	    ndiagram = {8,7,6,5,4,2};
	    tdiagram = {1};
	    f2diagram = {8,7,6,5,4,3,1};
	    rednode = 3;
	    Lreps = {
    	    	({1,1},{1}),
    	    	({1,1,1,1},{1,1}),
		({1,1,1,1,1,1},{2,1}),
		({2,1,1,1,1,1,1},{2,2})
    	    	};
	    )
	) else error "not implemented"
    ) else
if (c,t) == (4,1) then (
    if d == 2 then (
	g = lieAlgebra("E",6);
	ndiagram = {6,5,4,3,1};
	tdiagram = {};
	f2diagram = {6,5,4,3,2};
	rednode = 2;
	Lreps = {
	    ({1,1,1},{1}),
	    ({1,1,1,1,1,1},{2})
	    };
	) else
    if d == 3 then (
	g = lieAlgebra("E",7);
	ndiagram = {7,6,5,4,3,1};
	tdiagram = {};
	f2diagram = {7,6,5,4,3,2};
	rednode = 2;
	Lreps = {
	    ({1,1,1},{1}),
	    ({1,1,1,1,1,1},{2})
	    };
	) else
    if d == 4 then (
	excludeddiffs = {1};
	g = lieAlgebra("E",8);
	ndiagram = {8,7,6,5,4,3,1};
	tdiagram = {};
	f2diagram = {8,7,6,5,4,3,2};
	rednode = 2;
	Lreps = {
	    ({1,1,1},{1}),
	    ({1,1,1,1,1,1},{2}),
	    ({2,1,1,1,1,1,1,1},{3})
	    };
	) else error "not implemented"
    ) else
if (d,t) == (2,1) then (
    if c == 5 then (
	g = lieAlgebra("E",7);
	ndiagram = {1,3,4,5,6,7};
	tdiagram = {};
	rednode = 2;
	Lreps = {
	    ({1,1,1,1},{1}),
	    ({2,1,1,1,1,1,1},{2})
	    };
	) else
    if c == 6 then (
	g = lieAlgebra("E",8);
	ndiagram = {1,3,4,5,6,7,8};
	tdiagram = {};
	rednode = 2;
	Lreps = {
	    ({1,1,1,1,1},{1}),
	    ({2,2,1,1,1,1,1,1},{2}),
	    ({2,2,2,2,2,2,2,1},{3})
	    };
	) else error "not implemented"
    )

dnode = symbol dnode;
dnode_1 = bluenode = last ndiagram;
if c == 3 then (
    dnode_2 = first ndiagram;
    dnode_3 = last tdiagram;
    ) else
if c == 4 then (
    dnode_2 = first ndiagram;
    )

n = numrows g.cache#"CM"

V = symbol V; sref = new MutableHashTable;

if c == 3 then (
    for i in ({1,2,3}-set excludeddiffs) do (
    	V_i = extremalRepFull(g,dnode_i);
    	)
    ) else
if c == 4 then (
    for i in ({1,2}-set excludeddiffs) do (
    	V_i = extremalRepFull(g,dnode_i);
    	)
    ) else (
    V_1 = extremalRepFull(g,dnode_1)
    )

sln = slLie(QQ^(c+d))
slt = slLie(QQ^t)

ndiag = apply(ndiagram,i->i-1)
tdiag = apply(tdiagram,i->i-1)

ntdiag = ndiag|tdiag
slnt = sln++slt
incslnt = extendMap(slnt.cache#"e"|slnt.cache#"f",slnt,g.cache#"e"_ntdiag|g.cache#"f"_ntdiag,g);

F1 = subRep(sln,isl(QQ^(c+d)),QQ**antiDiagonalMatrix(c+d),glStandard(QQ^(c+d)));
Fc = subRep(slt,isl(QQ^(t)),QQ**antiDiagonalMatrix(t),glStandard(QQ^(t)));
FF1 = subRep(slnt,slnt^[0],id_(QQ^(c+d)),F1)
FFc = subRep(slnt,slnt^[1],id_(QQ^t),Fc)

if c == 3 then (
    f2diag = apply(f2diagram,i->i-1);
    slf2 = slLie(QQ^(d+t+2));
    incslf2 = extendMap(slf2.cache#"e"|slf2.cache#"f",slf2,g.cache#"e"_f2diag|g.cache#"f"_f2diag,g);
    F2 = subRep(slf2,isl(QQ^(d+t+2)),QQ**antiDiagonalMatrix(d+t+2),glStandard(QQ^(d+t+2)));
    ) else 
if c == 4 then (
    f2diag = apply(f2diagram,i->i-1);
    sof2 = lieAlgebra("D",c+d-1);
    incsof2 = extendMap(sof2.cache#"e"|sof2.cache#"f",sof2,g.cache#"e"_f2diag|g.cache#"f"_f2diag,g);
    F2 = extremalRepFull(sof2,1);
    )

--set up variables for cell
maxL = lift(maxEigenvalue(adjointRep g,rednode),ZZ)

L = symbol L;

LREPS = apply(Lreps, (i,j) -> schurRep(i,FF1)**schurRep(j,dualRep FFc))

adjrep = adjointRep g;
for i from 1 to #Lreps do (
    maplist = equivariantMaps(id_(module slnt),LREPS_(i-1),subRep(slnt,incslnt,gradedComponent(adjrep,rednode,i),adjrep));
    L_i = gradedComponent(adjrep,rednode,i)*(first maplist);
    )

indsL = apply(Lreps, (i,j) -> (number(i,k -> k == max i),number(j,k -> k == max j)))

--ring with all the variables that we might need
--i.e. symmetric algebra on the dual of the positive part of the Lie algebra in
--grading induced by red node
varsymbollist = {symbol x, symbol y, symbol z, symbol w, symbol u}
varlist = fold(
    apply(#indsL, m -> (
	    apply(subsets(1..(c+d),(indsL#m)_0)**subsets(1..t,(indsL#m)_1), l -> (varsymbollist_m)_(seqToNum(l_0),seqToNum(l_1)))
	    )
	),
    (i,j) -> i|j
    )
R1 = QQ[varlist]

--put grading by root lattice on this ring
Lgen = fold(apply(1..#Lreps,i->L_i),(i,j)->i|j)*genericMatrix(R1,numgens R1,1);
R = QQ[varlist,Degrees=>apply(varlist, tempx -> (
	    tempxring := QQ[tempx];
	    vecx := sub(sub(Lgen,tempxring),{tempxring_0=>1});
	    return (-flatten entries lift(((bracket g)*(g.cache#"h"**vecx))//vecx,ZZ))
	    )
    	)
    ];
Lgen = sub(Lgen,R);

end--
restart

(c,d,t) = (3,2,2);load "preparation.m2"

lambda = matrix{{0,1,0,0,0,0}}; sigmaraw = {};

lambda = matrix{{1,0,-1,0,1,0}}; sigmaraw = {3,4,2};

lambda = matrix{{0,1,-1,0,0,1}}; sigmaraw = {3,4,5,1,3,4,2};

lambda = matrix{{2,0,-1,0,0,0}}; sigmaraw = {3,4,2,5,4,6,5,3,4,2};

lambda = matrix{{1,0,-2,1,0,0}}; sigmaraw = {3,4,2,5,4,6,5,1,3,4,2};
lambda = matrix{{0,0,-1,0,0,1}}; sigmaraw = {3,4,2,5,4,3,1,3,4,2,5,4,6,5,3,4,2};

load "computation.m2"
F.dd







(c,d,t) = (6,2,1); load "preparation.m2"
lambda = matrix{{0, 0,  0, 0, 0, 0, 0, 1}}; sigmaraw = {}
lambda = matrix{{0, -1, 1, 0, 0, 0, 0, 0}}; sigmaraw = {2, 4, 5, 6, 7, 8}
lambda = matrix{{0, -1, 0, 0, 0, 1, 0, 0}}; sigmaraw = {2, 4, 5, 3, 4, 1, 3, 2, 4, 5, 6, 7, 8}
lambda = matrix{{1, -1, 0, 0, 0, 0, 0, 1}}; sigmaraw = {2, 4, 5, 6, 7, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1, 3, 2, 4, 5, 6, 7, 8}
lambda = matrix{{0, -2, 0, 1, 0, 0, 0, 0}}; sigmaraw = {2, 4, 5, 6, 7, 8, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1, 3, 2, 4, 5, 6, 7, 8}
lambda = matrix{{0, -1, 0, 0, 0, 0, 1, 0}}; sigmaraw = {2, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 4, 5, 6, 7, 8, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1, 3, 2, 4, 5, 6, 7, 8}
lambda = matrix{{1, -1, 0, 0, 0, 0, 0, 0}}; sigmaraw = {2, 4, 5, 6, 7, 8, 3, 4, 5, 6, 7, 2, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 4, 5, 6, 7, 8, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 4, 5, 3, 4, 1, 3, 2, 4, 5, 6, 7, 8}

load "computation.m2"
d1


S = ZZ/32003[x,y,z]
setRandomSeed "hello"
I = inverseSystem(random(S^{1:4},S^2))
