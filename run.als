open signatures
open carte
open temps

run progTemps for 10 but exactly 10 Time, exactly 2 Drone, exactly 6 Position, exactly 3 Commande, exactly 3 Receptacle

/* Cindy: 

-Le doc charges2.als a été renommé charges.als
-J'ai décidé de faire une simplification en rajoutant le fact NombreProduits dans charges : le nombre de produits d'une commande ne dépasse pas la charge d'un drone ou d'un réceptacle (donc on n'a plus besoin de la charge en temps réel d'un réceptacle)
-J'ai transformé le prédicat progCarte en fact => plus logique non ? A voir
-j'ai rajouté des assert qui sont valides et commentés dans charges, temps et carte
-on reste sur notre idée où on charge la batterie au max à chaque fois et on utilise la distance de manhattan
-on reste sur un nombre de commandes fixes à l'entrepôt au départ

A faire : 
	- cas où plusieurs drones en même temps => pb car les 2 drones prennent la même commande
	- cas où un drone est bloqué à un endroit car les positions suivantes sont occupées => il se passe quoi ? cas traité ?

*/
	
