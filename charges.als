open signatures

//Prédicats :


pred init [t:Time]
{
	all d : Drone, e:Entrepot, r:Receptacle | d.pos.t = e.pos && d.batterie.t = Int[1] && d.charge.t =Int[0] && r.charge.t = Int[5] && e.charge.t = Int[5]
}


pred surEntrepot [ d:Drone, t:Time] 
{
	some e:Entrepot | d.pos.t = e.pos
}

pred surReceptacle [ d:Drone , t:Time]
{
	some r:Receptacle | d.pos.t = r.pos
}


pred enDeplacement [ d:Drone, t:Time]
{
	!surEntrepot[d,t] //&& !surReceptacle[d,t] 
}

pred surBonReceptacle [ d:Drone , t:Time]
{
	d.pos.t = d.cmd.rec.pos
}

pred enDeplacement [ d:Drone, t:Time]
{
	t=last ||
	let t'=t.next
	{
		d.pos.t' != d.pos.t
	}
}
	

pred batteriePleine [d:Drone, t:Time]
{
	d.batterie.t = Int[3]
}


/* Un drone prend 1 unité de temps pour recharger sa batterie de 1 unité d'énergie */
pred chargeVide [ d:Drone, t:Time]
{	
	d.charge.t = Int[0]
}

/* Un drone prend 1 unité de temps pour recharger sa batterie de 1 unité d'énergie */
pred chargerBatterie [ d: Drone, t:Time]
{
	t=last ||
	let t' =t.next
	{
		d.batterie.t' = add[d.batterie.t, Int[1]]
	}	
}

/* Un drone consomme 1 unité d'énergie pour faire 1 pas sur la grille.
	Un drone prend 1 unité de temps pour se déplacer de 1 pas sur la grille.*/
pred dechargerBatterie [ d: Drone, t:Time]
{
	t=last ||
	let t' =t.next
	{
		d.batterie.t' = add[d.batterie.t, Int[-1]]
	}	
}


/* Une fois le réceptacle rejoint, l'action de livrer les produits prend 1 unité de temps. */
pred livrerProduits [ d: Drone, t:Time]
{
	1 = 0
	// remettre charge à 0
}

//Faits :
pred batterieConstante [ d: Drone, t:Time]
{
	t=last ||
	let t' =t.next
	{
		d.batterie.t' = d.batterie.t
	}	
}

pred chargeConstante [ d: Drone, t:Time]
{
	t=last ||
	let t' =t.next
	{
		d.charge.t' = d.charge.t
	}	
}

/* Une fois le réceptacle rejoint, l'action de livrer les produits prend 1 unité de temps. */
pred livrerProduits [ d: Drone, t:Time]
{
	t=last ||
	let t'=t.next
	{
		d.charge.t' = Int[0]
	}
}

/* Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */ 
pred chargerCommande [ d:Drone, t:Time]
{
	t=last ||
	let t'=t.next
	{
		d.charge.t' = Int[4]
	}
}

pred peutBouger{}

//Faits :



 /* La capacité de la batterie d'un drone est de 3 unités d'énergie */
fact capaciteBatterie
{
	all d : Drone, t : Time | d.batterie.t >= Int[0] && d.batterie.t <= Int[3]
}

/* Un drone a une capacité DCAP */
fact chargeDroneMaximum
{
	all d : Drone, c : Capacite, t : Time | ( (d.charge.t <= c.dcap) && (d.charge.t >= 0) )
}

/* Un réceptacle est un conteneur de capacité RCAP */
fact chargeReceptacleMaximum
{
	all r : Receptacle, c : Capacite, t : Time | ( (r.charge.t <= c.rcap) && (r.charge.t >= 0) )
}

/* Un drone peut recharger sa batterie au niveau de l'entrepôt.
	Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */ 
fact DroneEntrepot 
{	
//	init[first]
	all d : Drone, t :Time | (surEntrepot[d,t] && !batteriePleine[d,t]) => ( chargerBatterie[d,t] && surEntrepot[d,t.next])										
}

fact DroneDeplacement
{	
	all d : Drone, t :Time | enDeplacement[d,t] => dechargerBatterie[d,t]
}

//Assertions :

/* Un drone interagit avec un réceptacle pour y déposer les produits qu'il porte.	
	Un réceptacle permet aussi à un drone de recharger sa batterie. */
assert DroneReceptacle 
{		
	all d : Drone, t :Time | surReceptacle[d,t] => chargerBatterie[d,t]
}

// Entrepot 

/* Un drone peut recharger sa batterie au niveau de l'entrepôt. */	
fact BatterieEntrepot 
{		
	all d : Drone, t :Time| (surEntrepot[d,t] && chargeVide[d,t] && !batteriePleine[d,t]) => ( chargerBatterie[d,t] && !enDeplacement[d,t] && chargeConstante[d,t])										
}

fact ChargementEntrepot 
{
	all d:Drone, t:Time| (chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => chargerCommande[d,t] && !enDeplacement[d,t] && batterieConstante[d,t]
}

fact QuitterEntrepot
{
	all d:Drone, t:Time| ((peutBouger && !chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => (enDeplacement[d,t] && chargeConstante[d,t])) &&
																		((!peutBouger && !chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => (!enDeplacement[d,t] && chargeConstante[d,t] && batterieConstante[d,t] ))
}

// Receptacle

/* Un drone interagit avec un réceptacle pour y déposer les produits qu'il porte.	*/
fact LivraisonReceptacle 
{		
	all d : Drone, t :Time |  (surBonReceptacle[d,t] && !chargeVide[d,t] )=> ( livrerProduits[d,t] && !enDeplacement[d,t] && batterieConstante[d,t] )
}

/*	Un réceptacle permet aussi à un drone de recharger sa batterie. */
fact BatterieReceptacle 
{		
	all d : Drone, t :Time | (surReceptacle[d,t]  && !batteriePleine[d,t] ) => (chargerBatterie[d,t] && !enDeplacement[d,t]&& chargeConstante[d,t])
}

/*	Un réceptacle permet aussi à un drone de recharger sa batterie. */
fact BatterieBonReceptacle 
{		
	all d : Drone, t :Time | (surBonReceptacle[d,t] && chargeVide[d,t] && !batteriePleine[d,t] ) => (chargerBatterie[d,t] && !enDeplacement[d,t] && chargeConstante[d,t])
}

fact QuitterReceptacle 
{		
	all d : Drone, t :Time | ((peutBouger && batteriePleine[d,t] && surReceptacle[d,t]) =>  (enDeplacement[d,t] && chargeConstante[d,t])) &&
											((!peutBouger && batteriePleine[d,t] && surReceptacle[d,t]) =>  (!enDeplacement[d,t] && batterieConstante[d,t] && chargeConstante[d,t]))
}

fact DroneDeplacement
{	
	init[first]	
	all d : Drone, t :Time |  (enDeplacement[d,t] => dechargerBatterie[d,t] && chargeConstante[d,t]) &&									
											((!enDeplacement[d,t] && !surEntrepot[d,t] && !surReceptacle[d,t] )=> batterieConstante[d,t] && chargeConstante[d,t] )
}


//Assertions :


/* Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps */
assert NoLivraisonBatterie
{
	all d : Drone | no t :Time | livrerProduits[d,t] && chargerBatterie[d,t]
}

fact SortirDeEntrepot
{
	all d:Drone, t:Time | (batteriePleine[d,t] && surEntrepot[d,t]) => enDeplacement[d,t.next] 
}
