
open util/ordering[Position] as o

//Signatures :
sig Position
{
	nord : lone Position,
	est : lone Position,
	sud : lone Position,
	ouest : lone Position
}



one sig TopLeft extends Position {}

one sig TopRight extends Position {}

one sig BottomLeft extends Position {}

one sig BottomRight extends Position {}

fact 
{
	TopLeft.nord = none
	TopRight.nord = none
	TopRight.est = none
	BottomRight.est = none
	BottomRight.sud = none
	BottomLeft.sud = none
	BottomLeft.ouest = none
	TopLeft.ouest = none
	#TopLeft.sud = 1
	#TopRight.sud = 1
	#TopRight.ouest = 1
	#BottomRight.ouest = 1
	#BottomRight.nord = 1
	#BottomLeft.nord = 1
	#BottomLeft.est = 1
	#TopLeft.est = 1
}


pred positionRelations
{
	//On empeche les boucles
	all p : Position |  (  p.sud  != p and p.nord  !=  p and p.ouest  != p and p.est  != p )
	and 
	//On place géographiquement les points
	all p : Position |  	( 	(#p.sud = 0 or p = p.sud.nord) 
									and (#p.nord = 0 or p  =  p.nord.sud)
									and (#p.ouest = 0 or p = p.ouest.est) 
									and (#p.est = 0 or p  = p.est.ouest)
								)
	and 
	//On empèche les points isolés
	all p : Position | 	( #p.nord = 1 or #p.sud = 1 or #p.est = 1 or #p.ouest = 1 )
	and
	//On empèche d'avoir plusieurs relations entre deux points
	all p : Position |	( 	 (#p.sud= 0 or (p.sud != p.nord &&  p.sud != p.ouest &&  p.sud != p.est))
									and (#p.nord  =0 or ( p.nord != p.sud && p.nord != p.ouest &&  p.nord != p.est))
									and (#p.est= 0 or (p.est != p.nord && p.est != p.ouest && p.est != p.sud))
									and (#p.ouest = 0 or( p.ouest != p.nord &&  p.ouest != p.sud && p.ouest != p.est))
								)
	and
	//Création des limites du cadre
	all p : Position |  ( ( (#p.est = 1 and #p.est.nord = 0 and #p.nord = 0) or  (#p.est = 1 and #p.est.nord = 1 and #p.nord = 1)  or #p.est = 0) and
								  ( (#p.ouest = 1 and #p.ouest.nord = 0 and #p.nord = 0) or  (#p.ouest= 1 and #p.ouest.nord = 1 and #p.nord = 1) or #p.ouest = 0) and

								  ( (#p.est = 1 and #p.est.sud = 0 and #p.sud = 0) or  (#p.est = 1 and #p.est.sud = 1 and #p.sud = 1) or #p.est = 0) and
								  ( (#p.ouest = 1 and #p.ouest.sud = 0 and #p.sud = 0) or  (#p.ouest= 1 and #p.ouest.sud = 1 and #p.sud = 1) or #p.ouest = 0) and

								  ( (#p.nord = 1 and #p.nord.ouest = 0 and #p.ouest = 0) or  (#p.nord = 1 and #p.nord.ouest = 1 and #p.ouest = 1)  or #p.nord= 0) and
								  ( (#p.sud = 1 and #p.sud.ouest = 0 and #p.ouest = 0) or  (#p.sud= 1 and #p.sud.ouest = 1 and #p.ouest = 1) or #p.sud= 0 ) and

								  ( (#p.nord = 1 and #p.nord.est = 0 and #p.est = 0) or  (#p.nord = 1 and #p.nord.est = 1 and #p.est = 1)  or #p.nord= 0) and
								  ( (#p.sud = 1 and #p.sud.est = 0 and #p.est = 0) or  (#p.sud= 1 and #p.sud.est = 1 and #p.est = 1) or #p.sud= 0)
							    )
}

assert NoBadRelationsPosition
{
	positionRelations => no p1 : Position |  ( p1.sud = p1 or p1.nord =  p1
									or p1.ouest = p1 or p1.est = p1 )
	and
    positionRelations => no p  : Position | ( p != p.nord.sud and p !=  p.sud.nord
								     and p != p.est.ouest and p != p.ouest.est )
}

run positionRelations
check NoBadRelationsPosition for 5
