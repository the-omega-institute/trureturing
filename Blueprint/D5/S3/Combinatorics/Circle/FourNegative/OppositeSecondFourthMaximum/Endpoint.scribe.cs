using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite second/fourth maximum: joint orders",
        H("Original physical source and both strict sectors"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-opposite-second-fourth-maximum-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/OppositeSecondFourthMaximum/Endpoint.actualSource_opposite_second_fourth_maximum_joint_lift"),
                H("One original permutation, one literal ear, both totals and all repetitions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The quotient-mask construction follows the supplied Pro mathematical construction (SHA256 6895f9bcc25042ab2c2be58543673073aec889bd138a36637a1e4987dd9c7d1e).")),
                    Paragraph(Text("The exact original telescope is (a b c d : Nat), (ha : 2<=a), (hc : 2<=c), (hbd : b=d), (hab : a<b), (hcb : c<b), (hne : a different from c). The seed is exactly 1+2^a+2^(a+b)+2^(a+b+c), k is exactly a+b+c+d, and the enlarged seed is twice the original. No feasibility assumption, finite-range condition or excluded adjacent boundary is added.")),
                    Paragraph(Text("The endpoint first derives the quotient masks over both unbounded strict sectors, then applies the direct physical construction. It supplies one original sigma:List(Fin k) and a natural j<=k, with both OriginalOrder(k,seed,sigma) and OriginalOrder(k+1,2*seed,earWord(k,sigma,j)). The ear is the single new label k inserted at the literal list cut and immediately before original terminal k-1 in the construction.")),
                    Paragraph(Text("The endpoint explicitly includes every natural repetition count m and every natural take length n, after flattening List.replicate m of the old word and independently of the ear word. The old prefix lies in [0,modulus(k)/2] and the enlarged prefix lies in [0,modulus(k)]. Both complete repeated totals are zero for every m. OriginalOrder itself includes both individual period totals. The reused repeated_prefixes lemma proves the claims by append induction from the independently established zero totals.")),
                    Paragraph(Text("These quantifiers include zero repetitions, an empty take and overlong takes. A prefix of an already taken repeated list is another covered take, using List.take_take and the minimum of its two take lengths. The identity modulus(k+1)/2=modulus(k) converts the enlarged strip bound without changing any scalar source."))
                ), DescribeRole.Theorem)
        ), []));
}
