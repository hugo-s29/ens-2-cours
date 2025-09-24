# This file is a short tutorial made to help you visualize the execution of your programs using SMPI

It follows closely this simgrid tutorial : [simgrid.org](https://simgrid.org/doc/latest/Tutorial_MPI_Applications.html#lab-1-visualizing-lu).

It utilises the `pj_dump` [tool](https://github.com/schnorr/pajeng/wiki/pj_dump) to read execution traces produced by smpi. For this, you need the `pajeng` library. See [here](https://github.com/schnorr/pajeng/wiki/Install) for installation, or if you are on ubuntu simply run :  

``` 
sudo apt-get install pajeng
```

To generate a trace using smpirun, you need to add the `-trace` flag and set the trace output file with `--cfg=tracing/filename:trace.trace`. Below is an example of execution :  

```
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml -trace --cfg=tracing/filename:trace.trace ./bcast naive_bcast
```

Then, convert this trace to a csv file using `pj_dump` :

```
pj_dump trace.trace -z | grep ^State > trace.csv
```

The `-z` flag ignores parsing errors, and we filter to get only the State information of each process using `grep`.

Finally, use the provided python code to see the trace : 

```
python3 examine_trace.py trace.csv out.png
```

You might need to install the python libraries `pandas` and `matplotlib` if you do not have them already. You can achieve this by running : 

```
python3 -m pip install pandas matplotlib
```