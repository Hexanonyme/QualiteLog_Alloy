open signatures
open carte
open temps

pred prog 
{
	progCarte and progTemps
}

pred go{ prog }
run go for 4 but exactly 20 Time, exactly 1 Drone, exactly 4 Position, exactly 3 Commande, exactly 2 Receptacle


assert  a
{
	prog => all p : Position | Entrepot.pos = p
}
check a  for 4 but exactly 15 Time, exactly 1 Drone

/* Cindy: 

Problème réglé sur les commandes: elles s'enchaînent correctement et un drone ne reprend jamais la même commande 
=> une fois que toutes les commandes ont été livrées, le drone retourne à l'entrepot, se recharge en batterie et ne fait plus rien

Cas traité d'une commande qui a plus de produits que la capacité du receptacle : on livre en 2 fois avec un vidage du receptacle entre temps
==> la charge des receptacles est bien fixée sauf quand un drone arrive sur le receptacle de sa commande ==> la valeur change alors qu'elle doit être constante 
==> il faudrait faire marcher le fact ChargeBonReceptacle dans charges2

A faire : 
	- cas où un drone est bloqué à un endroit car les positions suivantes sont occupées => bien fixer tous les trucs qui doivent rester constants
	- cas où il y a plus de produits que la capacité de l'entrepot
	- sûrement plein d'autres choses ...	

NB: j'ai supprimé tous les trucs commentés dont j'étais (presque) sûre qu'ils étaient devenus inutiles
==>Si par mégarde j'ai effacé un truc important pour vous, désolée et vous pouvez le récupérer sur les anciennes versions git

*/
	
