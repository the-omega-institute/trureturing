using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite second/fourth maximum: endpoint candidate",
        H("Original physical source; full strict family; source only"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-opposite-second-fourth-maximum-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/OppositeSecondFourthMaximum/Endpoint.actualSource_opposite_second_fourth_maximum_joint_lift"),
                H("One original permutation, one literal ear, both totals and all repetitions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exact original telescope is (a b c d : Nat), (ha : 2<=a), (hc : 2<=c), (hbd : b=d), (hab : a<b), (hcb : c<b), (hne : a different from c). The seed is exactly 1+2^a+2^(a+b)+2^(a+b+c), k is exactly a+b+c+d, and the enlarged seed is twice the original. No feasibility assumption, finite-range condition or excluded adjacent boundary is added.")),
                    Paragraph(Text("The endpoint first derives the quotient masks over both unbounded strict sectors, then applies the direct physical construction. It supplies one original sigma:List(Fin k) and a natural j<=k, with both OriginalOrder(k,seed,sigma) and OriginalOrder(k+1,2*seed,earWord(k,sigma,j)). The ear is the single new label k inserted at the literal list cut and immediately before original terminal k-1 in the construction.")),
                    Paragraph(Text("The endpoint explicitly includes every natural repetition count m and every natural take length n, after flattening List.replicate m of the old word and independently of the ear word. The old prefix lies in [0,modulus(k)/2] and the enlarged prefix lies in [0,modulus(k)]. Both complete repeated totals are zero for every m. OriginalOrder itself includes both individual period totals. The reused repeated_prefixes lemma proves the claims by append induction from the independently established zero totals.")),
                    Paragraph(Text("These quantifiers include zero repetitions, an empty take and overlong takes. A prefix of an already taken repeated list is another covered take, using List.take_take and the minimum of its two take lengths. The identity modulus(k+1)/2=modulus(k) converts the enlarged strip bound without changing any scalar source.")),
                    Paragraph(Text("The Reg candidate mirrors this full four-parameter theorem through the existing enrolled dependent-family realize template. Its parameter space is the infinite dependent tuple of four natural parameters and its state is the infinite natural seed. The two finite roles select old and enlarged readouts; they do not replace the parameter family or its states with a finite table. The candidate includes an actual equivalence, variation, deletion of each readout, actual seed dependence, sourceSelection coordinates and continuation.unknown.")),
                    Paragraph(Text("The source-bound Reg contains no compiled binding evidence and has not been declared_validated. Its selector paths and template applications require later elaboration and the existing binding machinery. continuation.unknown records an unknown residual; it asserts neither undecidability nor infinite residual complexity.")),
                    Paragraph(Text("Attribution: the supplied immutable Pro construction text has SHA256 6895f9bcc25042ab2c2be58543673073aec889bd138a36637a1e4987dd9c7d1e. Mathematical and template library sources were read at local immutable pin 2b864d9791df87fad16e579bec3bfa788485c99f and their actual byte hashes are in source-manifest.json. The implementation is a single native codex-cli flight; no independent review was read and no consensus is claimed.")),
                    Paragraph(Text("This artifact delivers complete intended scripts for this specified strict family, subject to unperformed Lean and Reg elaboration. No compiler, Lake, build, worktree, child agent, Pro/oracle call, Git mutation, judge mutation or official acceptance was performed. The unchanged whole original Circle/J/C3.1 four-negative goal remains OPEN."))
                ), DescribeRole.Theorem)
        ), []));
}
