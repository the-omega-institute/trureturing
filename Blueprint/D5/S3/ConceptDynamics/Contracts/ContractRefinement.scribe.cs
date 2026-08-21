using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Contracts;

internal sealed class ContractRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong contracts imply their weaker contract obligations.",
        H("Contract Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strong-contract-refines-weak"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Contracts/ContractRefinement."
                        + "strong_contract_refines_weak"),
                H("A strong contract implies the weak contract"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A contract is represented by an allowed-input set and a "
                            + "guaranteed-output set for an explicit implementation map. "
                            + "The stronger contract accepts at least every input of the "
                            + "weaker one and allows at most its outputs.")),
                    Paragraph(Text(
                        "The public hypotheses state both subset relations and that the "
                            + "implementation maps every strong-contract input into the "
                            + "strong guarantee. The conclusion is the corresponding weak "
                            + "guarantee for every weak-contract input.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact contract "
                            + "refinement theorem. The proof applies the two source subset "
                            + "relations directly."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula SetOf(Formula type) =>
        Seq(Operatorname, Grp(F.Id("Set")), Sp, type);

    private static Formula Membership(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Formula()
    {
        Formula input = F.Id("I");
        Formula output = F.Id("O");
        Formula allowed = F.Id("A");
        Formula allowedPrime = F.Id("Aprime");
        Formula guaranteed = F.Id("G");
        Formula guaranteedPrime = F.Id("Gprime");
        Formula implementation = F.Id("M");
        Formula value = F.Id("i");
        Formula inputSets = Seq(
            allowed, Comma, Sp, allowedPrime, Colon, Sp, SetOf(input), Comma, Sp,
            guaranteed, Comma, Sp, guaranteedPrime, Colon, Sp, SetOf(output), Comma, Sp,
            implementation, Colon, Sp, input, Sp, To, Sp, output);
        Formula strongHypothesis = Seq(
            Forall, Sp, value, Colon, Sp, input, Comma, Sp,
            Membership(value, allowedPrime), Sp, Rightarrow, Sp,
            Membership(Apply(implementation, value), guaranteedPrime));
        Formula weakConclusion = Seq(
            Forall, Sp, value, Colon, Sp, input, Comma, Sp,
            Membership(value, allowed), Sp, Rightarrow, Sp,
            Membership(Apply(implementation, value), guaranteed));

        return Disp(Seq(
            Forall, Sp, input, Comma, Sp, output, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            inputSets, Comma, Esc,
            allowed, Sp, Subseteq, Sp, allowedPrime, Sp, Land, Sp,
            guaranteedPrime, Sp, Subseteq, Sp, guaranteed, Sp, Land, Sp,
            strongHypothesis, Sp, Rightarrow, Sp, weakConclusion, Dot));
    }
}
