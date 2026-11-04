using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class JMJPairLosingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete losing pairs below JMJ", H("Complete losing pairs below JMJ"), Blocks(
            Describe.Lean(DescribeId.Create("jmj-native-pair-losing-bridge"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/JMJPairLosing.jmj_pair_losing_iff"),
                H("Native failure at either fourth JMJ child"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let n be any natural number at least three, E either fourth action, and z and v arbitrary real numbers. Let W and Z be distinct complete legal cubic-gain worlds whose actual chronological JMJE readings are exactly (0,24,48,z,v). There is no source, drift, gain-ray or individual nonzero-sample promise. The same two-world support has native Losing n exactly when the drifts agree, both gains vanish at every original clock 4+j for 2 <= j <= n, and the actual fifth responses agree under each of J and M.")),
                    Paragraph(Text("For n=3 the zero condition consists precisely of gW(6)=gZ(6)=gW(7)=gZ(7)=0. Equality along every continuation forces common drift and the later zero gain samples. Equal sources would identify the coefficient vectors from the four shared ancestor readings at clocks zero through three, since every actual source trace there is positive; hence distinct worlds have distinct sources. The reverse implication constructs every entire response slice recursively: the common fifth value retains both worlds, and each later value is their common drift. Every node retains the two-world stopping guard.")),
                    Paragraph(Text("The characterization applies to both fourth children and all real z,v. It does not classify the quadratic roots at fourth J, determine the admissible interval or forced fourth response, exclude fourth M, or extract a losing pair from a larger support."))
                ), DescribeRole.Theorem)
        )));
}
