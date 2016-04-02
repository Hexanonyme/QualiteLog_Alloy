open signatures
open carte
open temps
pred prog 
{
	progCarte and progTemps
}

assert  a
{
	prog => all p : Position | Entrepot.pos = p
}

pred go{ prog }
run go for 4 but exactly 10 Time, exactly 1 Drone, exactly 4 Position, exactly 2 Commande

check a  for 4 but exactly 15 Time, exactly 1 Drone

/*PB: une même commande peut etre traité plusieurs fois 
le dcap, rcap n'est pas géré,
je mange trop de chocolat */
