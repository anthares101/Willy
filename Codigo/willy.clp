(defrule moveWilly
   (directions $? ?direction $?)
   =>
   (moveWilly ?direction)
   )

(defrule fireWilly
	(hasLaser)
	(directions $? ?direction $?)
	=>
	(fireLaser ?direction)
	)