newPackage(
    "DynkinPerfectIdeals",
    Version => "1.0",
    Date => "January 24, 2022",
    Authors => {
	{Name => "Xianglong Ni",
	    Email => "xlni@berkeley.edu",
	    HomePage => "https://math.berkeley.edu/~xlni/"
	    }
	},
    Headline => "(conjecturally) generic examples of perfect resolutions",
    AuxiliaryFiles => true,
    DebuggingMode => false
    )

export {
--    "LieAlgebraCache",
--    "fillBracket",
--    "Jacobi",
    "name",
    "newRep",
    "Ltog",
    "L0tog",
    "LieAlgebraRep",
    "newLieAlgebra",
    "LieAlgebra",
    "lieAlgebra",
    "truncateLieAlgebra",
    "action",
    "actionHT",
    "checkRep",
    "generate",
    "subRep",
    "quotientRep",
    "gl",
--    "igl",
    "tr",
    "wedgeDiag",
    "isl",
    "sl",
    "psl",
    "completeIrrepAction",
    "extendMap",
    "trivialRep",
    "invariants",
    "equivariantMaps",
    "weightSpace",
    "parametrizeCell",
    "glLie",
    "soLie",
    "slLie",
    "glStandard",
    "slStandard",
    "schurRep",
    "adjointRep",
    "tensorRep",
    "dualRep",
    "bracket",
    "repFromGradedAction",
    "completeGradedAction",
    "parametricAction",
    "extremalRep", --should be deprecated eventually
    "extremalRepFull",
    "genericMultigrade", --should be deprecated eventually
    "genericMultigradeFull",
    "topComplex",
    "genericGorIndexing",
    "subAlgebra",
--    "safeInc",
    "algebra",
    "Sign",
    "defectLieAlgebraDual",
    "formatLookup",
    "mapInfo"
    }

needsPackage "SchurFunctors"

------------------------------------------------
-- Cache for storing Lie algebra computations --
------------------------------------------------

LieAlgebraCache = new MutableHashTable;

---------------------
-- Auxiliary files --
---------------------

--wedgeDiag, working with reps, etc.
load "./DynkinPerfectIdeals/BasicMethods.m2"

--initializing Lie algebra data
load "./DynkinPerfectIdeals/LieAlgebras.m2"

--actually constructing the resolutions
load "./DynkinPerfectIdeals/GenericResolutions.m2"

end
uninstallPackage "DynkinPerfectIdeals"
restart
needsPackage "DynkinPerfectIdeals"
installPackage "DynkinPerfectIdeals"

--
F1 = QQ^9
g = slLie F1
F1rep = subRep(g, isl F1,id_F1,glStandard F1)

V0 = schurRep({1,1,1,1},F1rep)**schurRep({1,1,1},F1rep)

hwvec=invariants(
    g.cache#"e",
    V0);

((action V0)*(g.cache#"h"**hwvec_{0}))//hwvec_{0}
((action V0)*(g.cache#"h"**hwvec_{1}))//hwvec_{1}
((action V0)*(g.cache#"h"**hwvec_{2}))//hwvec_{2}
((action V0)*(g.cache#"h"**hwvec_{3}))//hwvec_{3}

--{1,1,1,1,1,1,1}
--{2,1,1,1,1,1}
--{2,2,1,1,1}
--{2,2,2,1}

equivariantMaps(
    id_(module g),
    V0,
    schurRep({1,1,1,1,1},F1)**F1**F1
    );
V1 = (
    
    
    
    )


F1rep = F1
F1 = QQ^7
--try to find 4 maps -> wedge^3 ** wedge^4
f1 = (
    flip(exteriorPower(4,F1),exteriorPower(3,F1))
    );
f2 = (
    (id_(exteriorPower(3,F1))**wedgeProduct(3,1,F1))
    *(flip(exteriorPower(3,F1),exteriorPower(3,F1))**id_F1)
    *(id_(exteriorPower(3,F1))**wedgeProduct(1,2,F1)**id_F1)
    *(wedgeDiag(3,1,F1)**wedgeDiag(2,1,F1))
    );
f3 = (
    (id_(exteriorPower(3,F1))**wedgeProduct(2,2,F1))
    *(flip(exteriorPower(2,F1),exteriorPower(3,F1))**id_(exteriorPower(2,F1)))
    *(id_(exteriorPower(2,F1))**wedgeProduct(2,1,F1)**id_(exteriorPower(2,F1)))
    *(wedgeDiag(2,2,F1)**wedgeDiag(1,2,F1))
    );
f4 = (
    (id_(exteriorPower(3,F1))**wedgeProduct(1,3,F1))
    *(wedgeDiag(3,1,F1)**id_(exteriorPower(3,F1)))
    );


fold(homomorphism'\(f1,f2,f3,f4),(a,b)->a|b);
rank oo

1683


slF3 = slLie(QQ^3)
F3 = subRep(slF3,isl(QQ^3),id_(QQ^3),glStandard(QQ^3))
slF1 = slLie(QQ^6)
F1 = subRep(slF1,isl(QQ^6),id_(QQ^6),glStandard(QQ^6))

sll = slF3++slF1

FF3 = subRep(sll,sll^[0],id_(QQ^3),F3)
FF1 = subRep(sll,sll^[1],id_(QQ^6),F1)

L1 = (dualRep FF3)**schurRep({1,1},FF1)

tmp = schurRep({1,1},L1)
load "testfile.m2" --has bracket data from first part of package

L2 = quotientRep(id_(module sll),sll,tmp,QQ**BB2)

tmp = schurRep({1,1},L1++L2)
L3 = quotientRep(id_(module sll),sll,tmp,QQ**BB3)



equivariantMaps(
    id_(module sll),
    L2compare,
    L2);

BB2;

L2 = schurRep({1,1},dualRep FF3)**schurRep({1,1,1,1},FF1)
