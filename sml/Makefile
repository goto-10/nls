# Suppress pointless polyEqual warning.
SMLFLAGS=-Ccontrol.poly-eq-warn=false

main:	neutrino.sml test.sml syntax.sml
	sml $(SMLFLAGS) test.sml
