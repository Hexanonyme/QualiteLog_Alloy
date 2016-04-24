open signatures

//Fonctions

fun manhattan [p1, p2 : Position ] : Int
{
		add [
			sub[
				larger  [p2.x, p1.x], 
				smaller [p2.x, p1.x]
			],	
			sub[
				larger  [p2.y, p1.y], 
				smaller [p2.y, p1.y]
			]
		]
}

//Prédicats

pred init 
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
	(Commande -> Receptacle).Receptacle = Entrepot.cmdALivrer
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
	and
	//Ajout des coordonnées
	all p : Position |  ((#p.ouest = 1 => p.x = add [p.ouest.x, Int[1]]) and  (#p.ouest = 0 => p.x =  Int[0]) and
							   ((#p.sud = 1 => p.y = add [p.sud.y, Int[1]]) and (#p.sud = 0 => p.y = 0) ) )
	and
	//Interdiction d'avoir plusieurs points aux mêmes coordonnées
	all p1, p2 : Position | (p1.x = p2. x and p1.y = p2.y) => p1 = p2
}

pred positionReceptacles
{
	all r : Receptacle | r.pos != Entrepot.pos
	and
	all r1, r2 : Receptacle | r1 != r2 => r1.pos != r2.pos 
}

// A un instant t, au plus drone peut interagir avec un réceptacle
// +
// A un instant t, il y a au plus un drone à chaque intersection de la grille
pred positionDrones
{
	all d1, d2 : Drone, t:Time | d1 != d2 => (d1.pos.t != d2.pos.t or (d1.pos.t = Entrepot.pos and d2.pos.t = Entrepot.pos))
}

// Il existe au moins un receptacle voisin de l'entrepot 
// +
// La distance entre tout couple d'élément consécutif de ce chemin doit être inférieur au égale à trois
pred eloignementReceptacle
{
	some r : Receptacle | eq[manhattan[r.pos, Entrepot.pos], Int[1]]
	and
	all r1, r2 : Receptacle | r1 != r2 => lte [manhattan[r1.pos, r2.pos], Int[3]]
}

//Faits

fact ProgCarte
{
	init and positionRelations and positionReceptacles and positionDrones and eloignementReceptacle
}

//Assertions

// Un réceptacle ne doit pas être sur l'entrepôt
// ==> vrai grâce à positionReceptacles
assert NoReceptacleOnEntrepot
{
	all r : Receptacle | r.pos != Entrepot.pos
}
check NoReceptacleOnEntrepot

// Deux réceptacles ne doivent pas avoir la même position
// ==> vrai grâce à positionReceptacles
assert DeuxReceptaclesPositions
{
	all r1, r2 : Receptacle | r1 != r2 => r1.pos != r2.pos
}
check DeuxReceptaclesPositions

// Il existe au moins un receptacle voisin de l'entrepot
// ==> vrai grâce à eloignementReceptacle 
assert VoisinEntrepot
{
	some r : Receptacle |  eq[manhattan[r.pos, Entrepot.pos],Int[1]]
}
check VoisinEntrepot 
