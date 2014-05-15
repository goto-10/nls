# Suppress pointless polyEqual warning.
SMLFLAGS=-Ccontrol.poly-eq-warn=false -Ctdp.instrument=true

FILES=         \
eval.sml       \
neutrino.sml   \
syntax.sml     \
test.sml       \
utils.sml      \
value.sml

main:	$(FILES)
	sml $(SMLFLAGS) test.sml
