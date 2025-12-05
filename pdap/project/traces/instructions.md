# This file is a short tutorial made to help you visualize the execution of your programs using SMPI

It follows closely this simgrid tutorial : [simgrid.org](https://simgrid.org/doc/latest/Tutorial_MPI_Applications.html#lab-1-visualizing-lu), but with a handmade paje parser to avoid downloading pajeng.

To generate a trace using smpirun, you need to add the `-trace` flag and set the trace output file with `--cfg=tracing/filename:trace.trace`. Below is an example of execution :  

```
smpirun -hostfile ring-32-hostfile.txt -platform ring-32-platform.xml -trace --cfg=tracing/filename:trace.trace ./bcast naive_bcast
```
Then, use the provided `tracer.py` file to examine the trace.


```
python3 tracer.py trace.trace
```

Optionnally if you want to save the figure to a file, do


```
python3 tracer.py trace.trace out.png
```