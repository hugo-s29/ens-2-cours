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
  cp cs/chap02.pdf ../web/public/data/ens2/cs-chap02.pdf

  cp pdap/td.pdf ../web/public/data/ens2/pdap-td.pdf
  cp pdap/project/report.pdf ../web/public/data/ens2/pdap-project.pdf

  cp cap/homework/main.pdf ../web/public/data/ens2/cap-homework.pdf

  cp category-theory/main.pdf ../web/public/data/ens2/category-theory.pdf

  cp sv/td.pdf     ../web/public/data/ens2/sv-td.pdf
  cp sv/main.pdf   ../web/public/data/ens2/sv.pdf
  cp sv/print.pdf   ../web/public/data/ens2/sv-print.pdf
  cp sv/print2.pdf   ../web/public/data/ens2/sv-print2.pdf
  cp sv/homework/main.pdf ../web/public/data/ens2/sv-homework.pdf
  cp sv/chap00.pdf ../web/public/data/ens2/sv-chap00.pdf
  cp sv/chap01.pdf ../web/public/data/ens2/sv-chap01.pdf
  cp sv/chap02.pdf ../web/public/data/ens2/sv-chap02.pdf
  cp sv/chap03.pdf ../web/public/data/ens2/sv-chap03.pdf
  cp sv/chap04.pdf ../web/public/data/ens2/sv-chap04.pdf
  cp sv/chap05.pdf ../web/public/data/ens2/sv-chap05.pdf
  cp sv/chap06.pdf ../web/public/data/ens2/sv-chap06.pdf
  cp sv/chap07.pdf ../web/public/data/ens2/sv-chap07.pdf
  cp sv/chap08.pdf ../web/public/data/ens2/sv-chap08.pdf
  cp sv/chap09.pdf ../web/public/data/ens2/sv-chap09.pdf

  cp opt/td.pdf     ../web/public/data/ens2/opt-td.pdf
  cp opt/revisions.pdf   ../web/public/data/ens2/opt-revisions.pdf
  cp opt/main.pdf   ../web/public/data/ens2/opt.pdf

  cp qcs/td.pdf     ../web/public/data/ens2/qcs-td.pdf
  cp qcs/assignment1.pdf ../web/public/data/ens2/qcs-assignment1.pdf
  cp qcs/assignment2.pdf ../web/public/data/ens2/qcs-assignment2.pdf
  cp qcs/assignment3.pdf ../web/public/data/ens2/qcs-assignment3.pdf
  cp qcs/assignment4.pdf ../web/public/data/ens2/qcs-assignment4.pdf
  cp qcs/assignment5.pdf ../web/public/data/ens2/qcs-assignment5.pdf
  cp qcs/assignment6.pdf ../web/public/data/ens2/qcs-assignment6.pdf
  cp qcs/assignment7.pdf ../web/public/data/ens2/qcs-assignment7.pdf
  cp qcs/assignment8.pdf ../web/public/data/ens2/qcs-assignment8.pdf
  cp qcs/assignment9.pdf ../web/public/data/ens2/qcs-assignment9.pdf
  cp qcs/revisions.pdf   ../web/public/data/ens2/qcs-revisions.pdf

  cp hott/partie1.pdf ../web/public/data/ens2/hott-partie1.pdf
  cp hott/partie2.pdf ../web/public/data/ens2/hott-partie2.pdf
  cp hott/partie3.pdf ../web/public/data/ens2/hott-partie3.pdf
  cp hott/partie4.pdf ../web/public/data/ens2/hott-partie4.pdf

  cp ip/presentation1.pdf ../web/public/data/ens2/ip-presentation1.pdf
  cp ip/usage_guide.pdf ../web/public/data/ens2/ip-usage-guide.pdf

  # ==========
  # SEMESTRE 2
  # ==========
  
  cp pp/td.pdf ../web/public/data/ens2/pp-td.pdf

  cp cc/td.pdf ../web/public/data/ens2/cc-td.pdf
  cp cc/main.pdf ../web/public/data/ens2/cc.pdf
  cp cc/chap01.pdf ../web/public/data/ens2/cc-chap01.pdf
  cp cc/chap02.pdf ../web/public/data/ens2/cc-chap02.pdf
  cp cc/chap03.pdf ../web/public/data/ens2/cc-chap03.pdf

  cp dbdm/td.pdf ../web/public/data/ens2/dbdm-td.pdf
  cp dbdm/homework.pdf ../web/public/data/ens2/dbdm-homework.pdf

  cp toplogie-algebrique/main.pdf ../web/public/data/ens2/topoalg.pdf
  cp toplogie-algebrique/td.pdf ../web/public/data/ens2/topoalg-td.pdf
fi
