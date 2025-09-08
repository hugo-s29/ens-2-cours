if [ "$HOSTNAME" = "s-1vcpu-1gb-lon1-01" ]; then
	cd /home/hugo/cours-m1/
	python3 tools/autocompress.py
else
	cd /Users/hugos29/Documents/ecole/ens2/
	ipython tools/autocompile.py
fi

if [ "$HOSTNAME" = "s-1vcpu-1gb-lon1-01" ]; then
  # cp all-m1.pdf ../web/public/data/ens1/all.pdf

  # ==========
  # SEMESTRE 1
  # ==========

  #cp pdap/main.pdf   ../web/public/data/ens2/pdap.pdf
  #cp pdap/chap00.pdf ../web/public/data/ens2/pdap-chap00.pdf
  #cp pdap/chap01.pdf ../web/public/data/ens2/pdap-chap01.pdf

  cp cs/main.pdf   ../web/public/data/ens2/cs.pdf
  cp cs/chap00.pdf ../web/public/data/ens2/cs-chap00.pdf
  cp cs/chap01.pdf ../web/public/data/ens2/cs-chap01.pdf

  cp cap/main.pdf   ../web/public/data/ens2/cap.pdf
  cp cap/chap00.pdf ../web/public/data/ens2/cap-chap00.pdf
  #cp cap/chap01.pdf ../web/public/data/ens2/cap-chap01.pdf


  # ==========
  # SEMESTRE 2
  # ==========
fi
