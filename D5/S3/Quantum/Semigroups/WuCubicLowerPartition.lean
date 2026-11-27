/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerPartition
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic partition from the lower near-Gibbs Wu cubic verifier. -/

import D5.S3.Quantum.Semigroups.WuCubicUpperPartition

namespace D5.S3.Quantum.Semigroups.WuCubicLowerPartition

open WuCubicUpperPartition (Box Tree)

def root : Box :=
  ![(1049 / 1000, 6 / 5), (-1 / 256, 0), (-1 / 256, 1 / 256), (0, 1)]

def tree : Tree :=
  (.split 0
    (.split 1
      (.split 2
        (.split 0
          (.split 0
            (.split 0
              (.split 3
                (.split 2
                  (.split 3
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 (.split 0 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)))
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)))))
                  (.split 0
                    (.split 3
                      (.split 2
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 0 (.split 1 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf)))
                      (.split 2
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                    (.split 3
                      (.split 2 (.split 0 (.split 3 .leaf .leaf) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))
                      (.split 2 (.split 0 (.split 3 .leaf .leaf) .leaf) (.split 0 .leaf .leaf)))))
                (.split 2
                  (.split 3
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 .leaf (.split 0 .leaf .leaf)) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 1 .leaf .leaf)))
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))))
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 .leaf (.split 0 .leaf .leaf)) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 0 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 .leaf .leaf)))
                      (.split 2
                        (.split 3 (.split 0 (.split 1 .leaf .leaf) .leaf) (.split 0 .leaf .leaf))
                        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)))))
                  (.split 0
                    (.split 3
                      (.split 2
                        (.split 0 (.split 1 .leaf (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf))
                        (.split 0 .leaf .leaf))
                      (.split 2 (.split 0 (.split 1 .leaf .leaf) .leaf) (.split 0 .leaf .leaf)))
                    (.split 3
                      (.split 2 (.split 0 (.split 1 .leaf .leaf) .leaf) (.split 0 .leaf .leaf))
                      (.split 2 (.split 0 .leaf .leaf) .leaf)))))
              (.split 3
                (.split 2
                  (.split 3
                    (.split 0 (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 2 .leaf .leaf))
                    (.split 0
                      (.split 2 (.split 3 .leaf (.split 0 .leaf .leaf)) (.split 0 .leaf .leaf))
                      (.split 2 (.split 3 .leaf .leaf) .leaf)))
                  (.split 0
                    (.split 3
                      (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                      (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))
                    (.split 3 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))))
                (.split 2
                  (.split 3
                    (.split 0
                      (.split 2 (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 0 .leaf .leaf))
                      (.split 2 (.split 3 .leaf .leaf) .leaf))
                    (.split 0
                      (.split 2 (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 0 .leaf .leaf))
                      (.split 2 (.split 3 .leaf .leaf) .leaf)))
                  (.split 0
                    (.split 3 (.split 2 (.split 0 .leaf .leaf) .leaf) (.split 2 (.split 0 .leaf .leaf) .leaf))
                    (.split 3 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))))))
            (.split 3
              (.split 0
                (.split 2
                  (.split 3 (.split 0 (.split 2 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf)))
                (.split 2
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))
              (.split 0
                (.split 2
                  (.split 3 (.split 0 (.split 2 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))
                  (.split 0 (.split 3 (.split 2 .leaf .leaf) .leaf) (.split 3 .leaf .leaf)))
                (.split 2
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                  (.split 0 (.split 3 .leaf .leaf) .leaf)))))
          (.split 0
            (.split 3
              (.split 0 (.split 2 (.split 3 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 .leaf .leaf))
              (.split 0 (.split 2 (.split 3 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 .leaf .leaf)))
            (.split 3 (.split 0 (.split 2 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))))
        (.split 0
          (.split 0
            (.split 0
              (.split 2
                (.split 3
                  (.split 0
                    (.split 2
                      (.split 3 (.split 0 (.split 1 .leaf .leaf) .leaf) (.split 0 .leaf .leaf))
                      (.split 0 .leaf .leaf))
                    (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) .leaf))
                  (.split 0 (.split 2 (.split 3 .leaf .leaf) .leaf) (.split 2 (.split 3 .leaf .leaf) .leaf)))
                (.split 0 (.split 2 (.split 3 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)))
              (.split 2
                (.split 3
                  (.split 0 (.split 2 (.split 3 .leaf .leaf) .leaf) (.split 2 .leaf .leaf))
                  (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
                (.split 2 (.split 0 .leaf .leaf) .leaf)))
            (.split 2
              (.split 0
                (.split 3 (.split 0 (.split 2 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))
                (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))
              (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))))
          (.split 0
            (.split 2 (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 0 .leaf .leaf))
            (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))))
      (.split 2
        (.split 0
          (.split 0
            (.split 3
              (.split 0
                (.split 2
                  (.split 3
                    (.split 0
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 .leaf (.split 0 .leaf .leaf))
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))))
                  (.split 3
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 0 (.split 1 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf)))
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 0 (.split 1 .leaf .leaf) .leaf)))
                    (.split 0
                      (.split 2
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 0 (.split 1 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf)))
                      (.split 2
                        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))
                        (.split 0 (.split 1 .leaf .leaf) .leaf)))))
                (.split 2
                  (.split 3
                    (.split 0 (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 2 .leaf .leaf))
                    (.split 0
                      (.split 2 (.split 3 .leaf (.split 0 .leaf .leaf)) (.split 3 .leaf .leaf))
                      (.split 2 (.split 3 .leaf .leaf) .leaf)))
                  (.split 3
                    (.split 0 (.split 2 (.split 3 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 .leaf .leaf))
                    (.split 0 (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 .leaf .leaf)))))
              (.split 0
                (.split 2
                  (.split 3
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf)))
                        (.split 3
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))
                    (.split 0
                      (.split 2
                        (.split 3
                          (.split 0 (.split 1 (.split 0 .leaf .leaf) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf))
                          (.split 0 (.split 1 (.split 0 .leaf .leaf) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf)))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                      (.split 2
                        (.split 3 (.split 0 (.split 1 .leaf .leaf) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))
                        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)))))
                  (.split 0
                    (.split 3
                      (.split 2
                        (.split 0
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))
                          (.split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                        (.split 0 (.split 1 .leaf (.split 3 .leaf .leaf)) (.split 1 .leaf .leaf)))
                      (.split 2
                        (.split 0
                          (.split 1 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))
                          (.split 1 .leaf (.split 3 .leaf .leaf)))
                        (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))))
                    (.split 3
                      (.split 2
                        (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))
                        (.split 0 (.split 1 .leaf .leaf) .leaf))
                      (.split 2 (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 0 .leaf .leaf)))))
                (.split 2
                  (.split 3
                    (.split 0
                      (.split 2
                        (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                        (.split 3 .leaf (.split 0 .leaf .leaf)))
                      (.split 2 (.split 3 .leaf .leaf) .leaf))
                    (.split 0
                      (.split 2 (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 0 .leaf .leaf))
                      (.split 2 (.split 3 .leaf .leaf) (.split 0 .leaf .leaf))))
                  (.split 0
                    (.split 3
                      (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                      (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))
                    (.split 3 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))))))
            (.split 3
              (.split 0
                (.split 2
                  (.split 3 (.split 0 (.split 2 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))
                  (.split 3 (.split 0 (.split 2 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf)))
                (.split 2
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))
              (.split 0
                (.split 2
                  (.split 3
                    (.split 0 (.split 2 .leaf .leaf) .leaf)
                    (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
                  (.split 0 (.split 3 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)) (.split 3 .leaf .leaf)))
                (.split 2
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
                  (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))))
          (.split 0
            (.split 3
              (.split 2 (.split 0 (.split 3 .leaf .leaf) .leaf) (.split 0 (.split 3 .leaf .leaf) .leaf))
              (.split 0 (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 2 .leaf .leaf)))
            (.split 3
              (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
              (.split 0 (.split 2 .leaf .leaf) .leaf))))
        (.split 0
          (.split 0
            (.split 0
              (.split 2
                (.split 3
                  (.split 0
                    (.split 2
                      (.split 3
                        (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))
                        (.split 0 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)))
                      (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)))
                    (.split 2
                      (.split 3 (.split 1 .leaf (.split 0 .leaf .leaf)) (.split 0 .leaf .leaf))
                      (.split 0 (.split 3 .leaf .leaf) .leaf)))
                  (.split 0
                    (.split 2
                      (.split 3 (.split 0 (.split 1 .leaf .leaf) .leaf) (.split 0 .leaf .leaf))
                      (.split 0 .leaf .leaf))
                    (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 .leaf .leaf))))
                (.split 2 (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 0 .leaf .leaf)))
              (.split 2
                (.split 3
                  (.split 0
                    (.split 2 (.split 3 .leaf .leaf) (.split 0 .leaf .leaf))
                    (.split 2 (.split 3 .leaf .leaf) .leaf))
                  (.split 0 (.split 2 (.split 3 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)))
                (.split 2 (.split 0 (.split 3 .leaf .leaf) .leaf) .leaf)))
            (.split 2
              (.split 0
                (.split 3
                  (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))
                  (.split 0 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf)))
                (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf)))
              (.split 0 (.split 2 (.split 0 .leaf .leaf) .leaf) (.split 2 .leaf .leaf))))
          (.split 0
            (.split 2 (.split 0 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) (.split 0 .leaf .leaf))
            (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))))))
    (.split 0
      (.split 0
        (.split 2
          (.split 3 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))
          (.split 2 (.split 0 .leaf .leaf) .leaf))
        (.split 2 (.split 3 .leaf (.split 0 .leaf .leaf)) (.split 2 .leaf .leaf)))
      (.split 0 (.split 2 (.split 3 .leaf .leaf) .leaf) (.split 2 .leaf .leaf))))

end D5.S3.Quantum.Semigroups.WuCubicLowerPartition
