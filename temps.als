open signatures
open carte
open charges2

//Prédicats
pred init [t:Time]
{
	all d : Drone, r:Receptacle | d.pos.t = Entrepot.pos 
	&& d.batterie.t = Int[1] 
	&& d.charge.t =Int[0] 
	&& r.charge.t = Int[0] 
	&& #d.cmd.t = 0 
	&& Entrepot.currentCmd.t = first
}

pred interdictionSaut  [t, t': Time, d: Drone]
{
	// enlevé: si on a livré et qu'on veut retourner à l'entrepot
	/*#d.cmd.t = 0 => d.pos.t' = d.pos.t else*/
	(d.pos.t' = d.pos.t.nord or d.pos.t' = d.pos.t.est or d.pos.t' = d.pos.t.sud or d.pos.t' = d.pos.t.ouest or positionConstante[d,t])
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
		and progEntrepot[d,t] 
		and progReceptacle[d,t] 
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
