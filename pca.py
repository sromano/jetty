import numpy as n
from matplotlib.mlab import PCA
import matplotlib.pyplot as plot


with open("features") as f:
    s = f.readlines()
foobar = []
for l in s:
    if len(l) > 1:
        foobar.append(map(float,l.split()))

a = n.array(foobar)
results = PCA(a)

fig = plot.figure()
ax = fig.add_subplot(111)
p1, = ax.plot(results.Y[:,0], results.Y[:,1], 'bo')
#p2, = ax.plot(results.Y[10:11,0], results.Y[10:11,1], 'go')
#p3, = ax.plot(results.Y[11:21,0], results.Y[11:21,1], 'ro')
#plot.legend([p1, p3, p2], ["anti-", "-tion", "anti- -tion"], loc='lower right', numpoints=1)
#plot.legend([p1, p2, p3], ["constant", "linear", "quadratic"], loc='lower right', numpoints=1)
plot.title("PCA on Affix Features")
plot.xlabel("Primary Component 1 of features")
plot.ylabel("Primary Component 2 of features")
plot.show()
