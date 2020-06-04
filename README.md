# README

This repository contains TLA+ specifications of various protocols used by wallets in the nitro protocol.

# Getting started

1. First, you'll need to [grab the TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).
2. The learning curve is pretty tough. These [videos](http://lamport.azurewebsites.net/video/videos.html) are a good, but dense intro. You're on your own.


## Getting started quickly

The TLA+ toolbox is pretty useful for writing your spec, since it nicely formats the spec, and includes tools for translating PlusCal algorithms and defining/running models.
But, if you just want to run some pre-defined models, it's easier to do it from the command line.


1. You'll still need to [grab the TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).
2. Read [this article](https://medium.com/@bellmar/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2).
3. If you didn't read the article, follow [these instructions](https://github.com/pmer/tla-bin#installation).
4. Try out a model: `tlc TwoParticipants -config Success.cfg`.
5. Try out a model that fails: `tlc TwoParticipants -config EveHasAlicesPrivateKey.cfg` // FIXME