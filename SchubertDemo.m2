needsPackage "DynkinPerfectIdeals"


--an example in Gr(2,5)
F = slStandard(QQ^5);
g = algebra F
V = schurRep({1,1},F)
--the extremal weight of wv used to define X
schubertweight = matrix{{-1,1,-1,1}} 
--the cell
cellweight = matrix{{0,0,-1,0}};
weightSpace(U,schubertweight);
--Plucker coordinates vanishing on X
schubertideal = gens trim ker dual generate(g.cache#"f",weightSpace(V,schubertweight),V);
--parametrization of the cell C
eY = (exp parametricAction(V,parametrizeCell(g,cellweight)))*weightSpace(V,cellweight);
--ideal of X intersect C inside of C
I = ideal((dual eY)*schubertideal)


--an E_6 example (the grade 4 a.c.i. in E_6/P_1) 
g = lieAlgebra("E",6)
V = extremalRepFull(g,1)
schubertweight = matrix{{0,1,0,0,-1,1}} 
cellweight = matrix{{0,0,0,0,0,-1}};
schubertideal = gens trim ker dual generate(g.cache#"f",weightSpace(V,schubertweight),V);
eY = (exp parametricAction(V,parametrizeCell(g,cellweight)))*weightSpace(V,cellweight); R = ring eY
I = ideal((dual eY)*schubertideal);
F = res I
matrix degrees F_1
