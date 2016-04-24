open signatures
open carte
open charges

//Prédicats
pred init [t:Time]
{
	all d : Drone | surEntrepot[d,t]
	&& batteriePleine[d,t]
	&& chargeVide[d,t]
	&& #d.cmd.t = 0 
	&& Entrepot.currentCmd.t = first
}

pred interdictionSaut  [t, t': Time, d: Drone]
{
	d.pos.t' = d.pos.t.nord or d.pos.t' = d.pos.t.est or d.pos.t' = d.pos.t.sud or d.pos.t' = d.pos.t.ouest or positionConstante[d,t]
}


pred moveDrone [t, t': Time, d: Drone] 
{
	let dest = destination[d, t],
	 newPos = closer [d.pos.t.nord, d.pos.t.est, d.pos.t.sud, d.pos.t.ouest, dest]
	{
		d.pos.t' = newPos
	}
    dechargerBatterie[d,t]
}

pred progTemps 
{
	init [first]
    all t: Time-last | let t' = t.next
    {
		all d : Drone |  interdictionSaut[t, t', d] 
		and progCharges[d,t]
		and ((!surEntrepot[d,t] && !surReceptacle[d,t] && !surBonReceptacle[d,t] && !batterieVide[d,t] ) =>  moveDrone [t, t', d]) 
		and ((!chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t] ) =>  moveDrone [t, t', d]) 
		and (( batteriePleine[d,t] && (surReceptacle[d,t] || surBonReceptacle[d,t])) => moveDrone [t, t', d])
	}
}


//Fonctions
fun closer [e1, e2, e3, e4, dest: Position] : Position
{
	let a = manhattan[e1, dest], 
		  b = manhattan[e2, dest], 
		  c = manhattan[e3, dest], 
		  d = manhattan[e4, dest], 
		  smallerManhattan = 	smaller [smaller [a, b], smaller [c, d] ] 
	|
		eq[smallerManhattan, a] => e1 else
		eq[smallerManhattan, b] => e2 else
		eq[smallerManhattan, c]=> e3 else
		e4
}

fun destination [d: Drone, t : Time] : Position
{
	#d.cmd.t= 1 => d.cmd.t.rec.pos else Entrepot.pos
}

//Assertions

// La batterie ne doit pas être supérieure à 3 ou être vide (ou négative évidemment) 
// ==> vrai grâce à la condition !batteriePleine à chaque fois qu'on fait chargerBatterie  et à !batterieVide quand on fait moveDrone (et donc dechargerBatterie)
assert Batterie
{
	all  t : Time |
	progTemps=> (all d : Drone | d.batterie.t <= Int[3] && d.batterie.t > Int[0] )
}
check Batterie

// La charge d'un drone doit toujours être égale au nombre de produits de sa commande, s'il en a une 
// ==> vrai grâce au fact ChargeConstante
assert ChargeDrone
{
	all t : Time|
	progTemps=> ( all d : Drone | d.charge.t = #d.cmd.t.produit )
}
check ChargeDrone

// Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps (sur le réceptacle de sa commande)
// ==> vrai grâce à la condition chargeVide (si !chargeVide, on livre et puis quand chargeVide, on recharge la batterie)
assert NonLivraisonBatterie
{
	all t : Time-last |
	progTemps=> ( no d : Drone | livrerProduits[d,t] && chargerBatterie[d,t] )
}
check NonLivraisonBatterie

// Un drone ne peut pas charger une commande et recharger sa batterie en même temps (à l'entrepôt)
// ==> vrai grâce à la condition batteriePleine (si !batteriePleine, on recharge la batterie et puis quand batteriePleine, on charge la commande)
assert NonCommandeBatterie
{
	all t : Time-last |
	progTemps=> ( no d : Drone | chargerCommande[d,t] && chargerBatterie[d,t] )
}
check NonCommandeBatterie

// Deux drones ne doivent pas avoir la même position, sauf sur l'entrepôt
// ==> vrai grâce à positionDrones
assert DeuxDronesPositions
{
	all t : Time, d1,d2 : Drone |
	progTemps => ( d1 != d2 =>  d1.pos.t != d2.pos.t or (d1.pos.t = Entrepot.pos and d2.pos.t = Entrepot.pos))
}
check DeuxDronesPositions

// La distance entre tout couple d'élément consécutif d'un chemin ne doit pas être supérieur à 3
// ==> vrai grâce à eloignementReceptacle
assert PositionReceptacle
{
	all r1, r2 : Receptacle |
	progTemps => (	r1 != r2 => manhattan[r1.pos, r2.pos] <= Int[3] )
}
check PositionReceptacle

/*

// Une commande ne peut être chargée que par un seul drone
assert NonMemeCommande
{
	all t:Time, d1,d2 : Drone |
	progTemps => (d1 != d2 => d1.cmd.t != d2.cmd.t )
}
check NonMemeCommande

// Une commande ne peut être livrée qu'une seule fois
assert CommandeLivraisonUnique
{
	all t:Time, d:Drone |
	progTemps => ( d.cmd.t != Entrepot.currentCmd.t )
}
check CommandeLivraisonUnique

*/
