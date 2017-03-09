import tensorflow as tf
import numpy as np
import sys

from trainingData import trainingData
from testingData import testingData

trainingInputs = np.array([ x for x,y in trainingData ])
trainingOutputs = np.array([ y for x,y in trainingData ])

def fullyConnectedLayer(x, w, b):
    return tf.add(tf.matmul(x, w), b)
# def radialBasisLayer(x,w):
#     print tf.shape(w)
#     print w
#     print tf.tile(x, 10)
#     assert False
#    return tf.exp(- (activations**2)/10.0)

H = [30,20]
learning_rate = 0.01

featureDimension = len(trainingData[0][0])
outputDimension = len(trainingData[0][1])

#print "From %d dimensions into %d"%(featureDimension,outputDimension)

x = tf.placeholder(tf.float32,[None,featureDimension])
t = tf.placeholder(tf.float32,[None,outputDimension])

w = { 'w1': tf.Variable(tf.random_normal([featureDimension,H[0]])),
      'w2': tf.Variable(tf.random_normal([H[0],H[1]])),
      'w3': tf.Variable(tf.random_normal([H[1],outputDimension]))
}
b = { 'b1': tf.Variable(tf.random_normal([H[0]])),
      'b2': tf.Variable(tf.random_normal([H[1]])),
      'b3': tf.Variable(tf.random_normal([outputDimension]))
}



h = tf.nn.sigmoid(fullyConnectedLayer(x, w['w1'], b['b1']))
h = tf.nn.sigmoid(fullyConnectedLayer(h, w['w2'], b['b2']))
#radialBasisLayer(x,w['w1'])
epsilon = 0.00001
y = tf.log(tf.nn.sigmoid(fullyConnectedLayer(h, w['w3'], b['b3'])) + epsilon)

loss = tf.reduce_sum((t - y)**2)

optimizer = tf.train.AdamOptimizer(learning_rate=learning_rate).minimize(loss)
saver = tf.train.Saver()

if __name__ == '__main__':
    
    if sys.argv[1] == 'train':
        print "Training recognition model..."
        with tf.Session() as s:
            s.run(tf.initialize_all_variables())
            for i in range(10000):
                if i%100 == 0:
                    _,l = s.run([optimizer, loss], feed_dict = {x: trainingInputs, t: trainingOutputs})
                    print "Average loss @ iteration %d: %f"%(i,l/len(trainingData))
                else:
                    s.run([optimizer], feed_dict = {x: trainingInputs, t: trainingOutputs})
            print "Done with training and now will save to model.checkpoint"
            saver.save(s, "model.checkpoint")
    else:
        with tf.Session() as s:
            saver.restore(s, "model.checkpoint")
            print "\n".join([ "\n".join([ str(p) for p in v]) for v in s.run(y,feed_dict = {x: np.array(testingData)}) ])
        
