using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class IndexedReadoutMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enlarging a finite index set refines its dependent joint readout and shrinks "
            + "its equality kernel.",
        H("Indexed Readout Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("larger-index-sets-refine-joint-readouts"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementFactorization/IndexedReadoutMonotonicity."
                        + "indexed_readout_monotonicity"),
                H("Larger index sets refine joint readouts"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a dependent readout family q_i : X -> O_i and a finite index "
                            + "set J, the readout q_J records exactly the coordinates in J.")),
                    Paragraph(Text(
                        "When J is contained in K, coordinate restriction from the K-output "
                            + "to the J-output is a forgetting map. This directly witnesses "
                            + "that q_K refines q_J.")),
                    Paragraph(Text(
                        "Equality of the K-readouts can be evaluated at every coordinate "
                            + "coming from J. Hence every pair identified by q_K is also "
                            + "identified by q_J, giving the reverse kernel inclusion."))),
                DescribeRole.Theorem))));

    private static Formula MonotonicityFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("O");
        Formula readout = F.Id("q");
        Formula index = F.Id("i");
        Formula smaller = F.Id("J");
        Formula larger = F.Id("K");
        Formula inclusion = F.Id("hJK");
        Formula smallerReadout = new Formula.Subscript(F.Id("q"), smaller);
        Formula largerReadout = new Formula.Subscript(F.Id("q"), larger);

        return Disp(Seq(
            Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp, type, Comma, Sp,
            outputFamily, Colon, Sp, Arrow(indexType, type), Comma, Sp,
            readout, Colon, Sp,
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Arrow(stateType, Apply(outputFamily, index)), Comma, Sp,
            smaller, Comma, Sp, larger, Colon, Sp,
            Call("Finset", indexType), Comma, Sp,
            inclusion, Colon, Sp, smaller, Sp, Subseteq, Sp, larger, Comma, Sp,
            Call("Refines", smallerReadout, largerReadout), Sp, Land, Sp,
            Call("ker", largerReadout), Sp, Subseteq, Sp,
            Call("ker", smallerReadout), Dot));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
}
