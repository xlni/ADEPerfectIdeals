
Rs = prune (R/(ideal select(gens R, i -> (matrix{degree i}*(transpose lambda))_(0,0) <= 0)))
YY = sub(Lgen,Rs)

bot = symbol bot; top2 = symbol top2;
if c == 3 then (
    botreps = {,FF1,dualRep FF1,FFc};
    topreps2 = {,trivialRep slf2,F2,dualRep F2};
    for i in ({1,2,3}-set excludeddiffs) do (
    	mm := maxEigenvalue(V_i,rednode);
    	bot_i = gradedComponent(dualRep V_i,rednode,-mm)*(
	    first equivariantMaps(id_(module slnt),botreps#i,subRep(slnt,incslnt,gradedComponent(dualRep V_i,rednode,-mm),dualRep V_i))
	    )
    	);
    for i in ({1,2,3}-set excludeddiffs) do (
	mm := maxEigenvalue(V_i,bluenode);
    	top2_i = gradedComponent(V_i,bluenode,mm)*(
	    first equivariantMaps(id_(module slf2),topreps2#i,subRep(slf2,incslf2,gradedComponent(V_i,bluenode,mm),V_i))
	    )
	);
    if not member(1,excludeddiffs) then d1 = map(Rs^1,,(dual top2_1)*(dual((exp parametricAction(V_1,YY))*simpleRefAction(sigmaraw,V_1)))*bot_1);
    if not member(2,excludeddiffs) then d2 = (dual bot_2)*((exp parametricAction(V_2,YY))*simpleRefAction(sigmaraw,V_2))*top2_2;
    if not member(3,excludeddiffs) then d3 = (dual top2_3)*(dual((exp parametricAction(V_3,YY))*simpleRefAction(sigmaraw,V_3)))*bot_3;
    if #excludeddiffs == 0 then F = chainComplex(d1,d2 = map(source d1,,d2),d3 = map(source d2,,d3));
    ) else
if c == 4 then (
    botreps = {,FF1,dualRep FF1};
    topreps2 = {,trivialRep sof2,F2};
    for i in ({1,2}-set excludeddiffs) do (
	mm := maxEigenvalue(V_i,rednode);
    	bot_i = gradedComponent(dualRep V_i,rednode,-mm)*(
	    first equivariantMaps(id_(module slnt),botreps#i,subRep(slnt,incslnt,gradedComponent(dualRep V_i,rednode,-mm),dualRep V_i))
	    )
	);
    for i in ({1,2}-set excludeddiffs) do (
	mm := maxEigenvalue(V_i,bluenode);
    	top2_i = gradedComponent(V_i,bluenode,mm)*(
	    first equivariantMaps(id_(module sof2),topreps2#i,subRep(sof2,incsof2,gradedComponent(V_i,bluenode,mm),V_i))
	    )
	);
    if not member(1,excludeddiffs) then (
	d1 = map(Rs^1,,(dual top2_1)*(dual((exp parametricAction(V_1,YY))*simpleRefAction(sigmaraw,V_1)))*bot_1);
	d4 = dual d1;
	);
    if not member(2,excludeddiffs) then (
	d2 = (dual bot_2)*((exp parametricAction(V_2,YY))*simpleRefAction(sigmaraw,V_2))*top2_2;
	selfdual = first equivariantMaps(id_(module sof2),dualRep F2,F2);
	d3 = selfdual*(dual d2);
	);
    if #excludeddiffs == 0 then F = chainComplex(d1,d2 = map(source d1,,d2),d3 = map(source d2,,d3),d4 = map(source d3,,d4));
    ) else (
    --remaining cases only have first differential implemented
    mm = maxEigenvalue(V_1,rednode);
    bot_1 = gradedComponent(dualRep V_1,rednode,-mm)*(
	first equivariantMaps(id_(module slnt),FF1,subRep(slnt,incslnt,gradedComponent(dualRep V_1,rednode,-mm),dualRep V_1))
	);
    d1 = map(Rs^1,,
	(dual gradedComponent(V_1,bluenode,maxEigenvalue(V_1,bluenode)))
	*(dual((exp parametricAction(V_1,YY))*simpleRefAction(sigmaraw,V_1)))
	*bot_1
	)
    )
