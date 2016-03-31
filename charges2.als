open signatures

//Prédicats :


pred surEntrepot [ d:Drone, t:Time] 
{
	some e:Entrepot | d.pos.t = e.pos
}

pred surReceptacle [ d:Drone , t:Time]
{
	some r:Receptacle | d.pos.t = r.pos
}

pred init [t:Time]
{
	all d : Drone, e:Entrepot, r:Receptacle | d.pos.t = e.pos && d.batterie.t = Int[1] && d.charge.t =Int[0] && r.charge.t = Int[5] && e.charge.t = Int[5]
}


/*pred surBonReceptacle [ d:Drone , t:Time]
{
	d.pos.t = d.cmd.rec.pos
}*/

pred enDeplacement [ d:Drone, t:Time]
{
	let t' =t.next
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
	let t' =t.next
	{
		(d.batterie.t != Int[3]) =>(d.batterie.t' = add[d.batterie.t, Int[1]]) else (d.batterie.t' = add[d.batterie.t, Int[3]])
	}
}

/* Un drone consomme 1 unité d'énergie pour faire 1 pas sur la grille.
	Un drone prend 1 unité de temps pour se déplacer de 1 pas sur la grille.*/
pred dechargerBatterie [ d: Drone, t:Time]
{
	let t' =t.next
	{
		(d.batterie.t != Int[0] )=>(d.batterie.t' = add[d.batterie.t, Int[-1]]) else (d.batterie.t' = add[d.batterie.t, Int[0]])
	}
}

//Faits :
pred batterieConstante [ d: Drone, t:Time]
{
	let t' =t.next
	{
	d.batterie.t' = d.batterie.t
	}
}

pred chargeConstante [ d: Drone, t:Time]
{
	let t' =t.next
	{
	d.charge.t' = d.charge.t
	}
}

/* Une fois le réceptacle rejoint, l'action de livrer les produits prend 1 unité de temps. */
pred livrerProduits [ d: Drone, t:Time]
{
	let t' =t.next
	{
	d.charge.t' = Int[0]
	}
}

/* Les commandes sont gérées au niveau de l'entrepôt qui les reçoit par internet */ 
pred chargerCommande [ d:Drone, t:Time]
{
	let t' =t.next
	{
	d.charge.t' = Int[4]
	}
}


/*	Un réceptacle permet aussi à un drone de recharger sa batterie. */
/*pred BatterieReceptacle[d: Drone, t:Time]
{		
	 (surReceptacle[d,t]  && !batteriePleine[d,t] ) => (chargerBatterie[d,t] && !enDeplacement[d,t]&& chargeConstante[d,t])
}*/

pred BatterieEntrepot[d: Drone, t:Time] 
{
	(surEntrepot[d,t] && chargeVide[d,t] && !batteriePleine[d,t]) => ( chargerBatterie[d,t] && !enDeplacement[d,t] && chargeConstante[d,t])								
}

pred ChargementEntrepot[d: Drone, t:Time]
{
	(chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => chargerCommande[d,t] && !enDeplacement[d,t] && batterieConstante[d,t]
}

pred QuitterEntrepot[d: Drone, t:Time]
{
	((peutBouger && !chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => (enDeplacement[d,t] && chargeConstante[d,t])) &&
																		((!peutBouger && !chargeVide[d,t] && batteriePleine[d,t] && surEntrepot[d,t]) => (!enDeplacement[d,t] && chargeConstante[d,t] && batterieConstante[d,t] ))
}
pred peutBouger{}

//Receptacle
/* Un drone interagit avec un réceptacle pour y déposer les produits qu'il porte.	*/
/*pred LivraisonReceptacle[d: Drone, t:Time] 
{		
	(surBonReceptacle[d,t] && !chargeVide[d,t] )=> ( livrerProduits[d,t] && !enDeplacement[d,t] && batterieConstante[d,t] )
}

/*	Un réceptacle permet aussi à un drone de recharger sa batterie. */
/*pred BatterieReceptacle[d: Drone, t:Time] 
{		
	(surReceptacle[d,t]  && !batteriePleine[d,t] ) => (chargerBatterie[d,t] && !enDeplacement[d,t]&& chargeConstante[d,t])
}*/


pred Deplacement[d: Drone, t:Time]
{
	(enDeplacement[d,t] => (dechargerBatterie[d,t] && chargeConstante[d,t] )) and
	((!enDeplacement[d,t] && !surReceptacle[d,t] && !surEntrepot[d,t])=>batterieConstante[d,t] && chargeConstante[d,t])
}


pred progEntrepot[d:Drone ,t:Time]
{
	BatterieEntrepot[d,t] and ChargementEntrepot[d,t] and QuitterEntrepot[d,t]
}

/*pred progReceptacle[d:Drone ,t:Time]
{
	BatterieReceptacle[d,t] and ChargementReceptacle[d,t] and QuitterReceptacle[d,t]
}*/

//Faits :

fact traces 
{
	init [first]
    all t: Time-last
    {
		all d : Drone |  progEntrepot[d,t] and Deplacement[d,t]
	}
}
//Assertions :
