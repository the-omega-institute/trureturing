using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class TwelveStateComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native positive stationary hidden components", H("Native positive stationary hidden components"),
        Blocks(
            Paragraph(Text("Every component is a restriction of the original alternative presentation: it uses the same marked entries and a positive normalization of its actual stationary row. The conclusion concerns complete output measures on the original emitted-bit clock.")),
            Describe.Lean(DescribeId.Create("ergodic-native-component-law"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.ergodic_native_component_law"),
                H("A native stationary component of an ergodic output law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any stationary finite marked presentation θ whose output law is ergodic, every finite original hidden subset C and stationary restriction κ with the same marked entries and c times its stationary masses equal to the original masses, for some positive c, has complete visible law equal to θ. Restricted word path sums give scaled cylinder domination. A finite symmetric window partitions each measurable cylinder into original word atoms. Approximation under the sum of the two probability measures extends domination to absolute continuity on all output events. Stationarity of κ and ergodic extremality then give equality. The exact actual-native-component theorem consumes this helper; it also supplies the general ergodic-component clause of the supported-word obstruction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-native-component"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.actual_native_component"),
                H("Every positive native irreducible component retains the same actual law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite stationary presentation θ with complete visible law equal to the twelve-state P, every finite hidden subset C, every stationary stochastic presentation κ on C and every positive real weight c, assume c times κ.initial(i) equals θ.initial(i), and every κ marked entry is the corresponding original θ entry. If κ has positive-power reachability between every pair, its complete visible law equals P and all its word products exclude nonempty exact positive rectangular support. The proof first bounds the actual restricted path sums and every scaled cylinder mass by the original ones, extends that domination to absolute continuity on the complete bilateral output space, and uses original output ergodicity and component stationarity. It then applies the actual same-law irreducible obstruction. Periodic components remain allowed; zero-weight ghosts remain outside this conclusion."))), DescribeRole.Theorem))));
}
