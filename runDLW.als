open signatures
open carte
open temps


pred prog 
{
	progCarte and progTemps
}

check AssertDronePosition for 8
check NoReceptacleOnEntrepot for 10
check AssertPositionReceptacle for 7
run prog for 4 but exactly 9  Position, exactly 4 Receptacle, exactly 2 Drone

