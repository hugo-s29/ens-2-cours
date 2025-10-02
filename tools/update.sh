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

  cp cs/td.pdf     ../web/public/data/ens2/cs-td.pdf
  cp cs/main.pdf   ../web/public/data/ens2/cs.pdf
  cp cs/chap00.pdf ../web/public/data/ens2/cs-chap00.pdf
  cp cs/chap01.pdf ../web/public/data/ens2/cs-chap01.pdf

  cp cap/main.pdf   ../web/public/data/ens2/cap.pdf
  cp cap/chap00.pdf ../web/public/data/ens2/cap-chap00.pdf

  cp pdap/td.pdf ../web/public/data/ens2/pdap-td.pdf

  cp sv/td.pdf     ../web/public/data/ens2/sv-td.pdf
  cp sv/main.pdf   ../web/public/data/ens2/sv.pdf
  cp sv/chap00.pdf ../web/public/data/ens2/sv-chap00.pdf
  cp sv/chap01.pdf ../web/public/data/ens2/sv-chap01.pdf
  cp sv/chap02.pdf ../web/public/data/ens2/sv-chap02.pdf
  cp sv/chap03.pdf ../web/public/data/ens2/sv-chap03.pdf
  cp sv/chap04.pdf ../web/public/data/ens2/sv-chap04.pdf

  cp opt/td.pdf     ../web/public/data/ens2/opt-td.pdf
  cp opt/main.pdf   ../web/public/data/ens2/opt.pdf
  cp opt/chap00.pdf ../web/public/data/ens2/opt-chap00.pdf

  cp qcs/td.pdf     ../web/public/data/ens2/qcs-td.pdf
  cp qcs/main.pdf   ../web/public/data/ens2/qcs.pdf
  cp qcs/chap00.pdf ../web/public/data/ens2/qcs-chap00.pdf
  cp qcs/chap01.pdf ../web/public/data/ens2/qcs-chap01.pdf
  cp qcs/chap02.pdf ../web/public/data/ens2/qcs-chap02.pdf
  cp qcs/assignment1.pdf ../web/public/data/ens2/qcs-assignment1.pdf
  cp qcs/assignment2.pdf ../web/public/data/ens2/qcs-assignment2.pdf
  cp qcs/assignment3.pdf ../web/public/data/ens2/qcs-assignment3.pdf

  cp hott/partie1.pdf ../web/public/data/ens2/hott-partie1.pdf
  cp hott/partie2.pdf ../web/public/data/ens2/hott-partie2.pdf


  # ==========
  # SEMESTRE 2
  # ==========
fi
