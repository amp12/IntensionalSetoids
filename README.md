# IntensionalSetoids

### [github.com/amp12/IntensionalSetoids](https://github.com/amp12/IntensionalSetoids)

A semantics of extensional type theory with universes (ETU) is constructed within Agda with options `--safe` `--without-K`, used as a machine-checkable formalization of intentional type theory augmented with a universe closed under inductive-recursive definitions (ITU). The model of ETU uses a simple, but apparently new variation on the notion of displayed setoids. The syntax of ETU is defined in Agda in a traditional extrinsic form, using the [WSLN](https://github.com/amp12/WSLN) library for the well-scoped locally nameless representation of syntax. Giving its semantics in the setoid model is complicated by the very limited means of expression afforded by ITU. As a corollary we obtain a proof of the consistency of ETU within ITU.

### [Browsable code](https://amp12.github.io/IntensionalSetoids/html/README.html)

Checked with Agda version 2.8.0 using options

  `--safe`
  `--without-K`
  `--no-postfix-projections`
  
  
