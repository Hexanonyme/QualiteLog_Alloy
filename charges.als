open signatures

//Prédicats :

pred init [t:Time]
{
	all d : Drone, e:Entrepot, r:Receptacle | d.pos.t = e.pos && d.batterie.t = Int[1] && d.charge.t =Int[0] && r.charge.t = Int[0]
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

pred batteriePleine [d:Drone, t:Time]
{
	d.batterie.t = Int[3]
}

/* Un drone prend 1 unité de temps pour recharger sa batterie de 1 unité d'énergie */
pred chargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		d.batterie.t' = add[d.batterie.t, Int[1]]
	}	
}

/* Un drone consomme 1 unité d'énergie pour faire 1 pas sur la grille.
	Un drone prend 1 unité de temps pour se déplacer de 1 pas sur la grille.*/
pred dechargerBatterie [ d: Drone, t:Time]
{
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
	init[first]
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

/* Un drone ne peut pas livrer ses produits et recharger sa batterie en même temps */
assert NoLivraisonBatterie
{
	all d : Drone | no t :Time | livrerProduits[d,t] && chargerBatterie[d,t]
}

fact SortirDeEntrepot
{
	all d:Drone, t:Time | (batteriePleine[d,t] && surEntrepot[d,t]) => enDeplacement[d,t.next] 
}
