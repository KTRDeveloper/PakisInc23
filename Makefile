all:
	##################################################
	###               kissat_mab                   ###
	##################################################
	chmod a+x kissat_inc/configure kissat_inc/scripts/*.sh
	cd kissat_inc && ./configure --quiet --compact --no-proofs
	+ $(MAKE) -C kissat_inc

	##################################################
	###                 PaInleSS                   ###
	##################################################
	+ $(MAKE) -C painless-src
	mv painless-src/painless PaKis

clean:
	##################################################
	###                 PaInleSS                   ###
	##################################################
	+ $(MAKE) clean -C painless-src
	+ $(MAKE) clean -C kissat_inc
	rm -f PaKis
