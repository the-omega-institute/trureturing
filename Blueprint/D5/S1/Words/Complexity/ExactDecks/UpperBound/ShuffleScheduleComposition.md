# ShuffleScheduleComposition

## Abstract

Binary schedules compose into valid indexed schedules for all factors.

This module privately composes a binary shuffle of the first factor with an indexed schedule for the remaining factors. The resulting schedule preserves every source occurrence, evaluates to the same interleaved word, and supplies the schedule witness for each iterated ordinary shuffle.

## References

- Dependency: [D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration](OverlapInfiltration.md)
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation](../../ShuffleOrders/Binary/BinaryScheduleEvaluation.md)
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave](../../ShuffleOrders/Indexed/IndexedScheduleWeave.md)
