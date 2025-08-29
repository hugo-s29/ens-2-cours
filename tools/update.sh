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
  # SEMESTRE 2
  # ==========


  # ==========
  # SEMESTRE 1
  # ==========

  echo "It's compile time!"

fi
