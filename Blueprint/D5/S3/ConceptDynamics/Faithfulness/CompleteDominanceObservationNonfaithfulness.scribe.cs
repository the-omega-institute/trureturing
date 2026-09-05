using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class CompleteDominanceObservationNonfaithfulnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/CompleteDominanceObservationNonfaithfulness."
            + "complete_dominance_observation_nonfaithfulness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete dominance between distinct realized genotypes requires a nonfaithful "
            + "observation language and disappears under a separating readout.",
        H("Complete Dominance and Observation Nonfaithfulness"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-dominance-observation-nonfaithfulness"),
            DeclarationHandle.Create(Declaration),
            H("Complete dominance requires observation nonfaithfulness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A deterministic realization maps unordered diploid genotypes and a "
                        + "context to internal states. The canonical joint readout collects all "
                        + "coordinates of the chosen observation language.")),
                Paragraph(Text(
                    "Complete dominance identifies the profiles of the left homozygote and "
                        + "heterozygote while separating the heterozygote from the right "
                        + "homozygote. If the first two internal states are distinct, their "
                        + "shared profile makes the language noninjective on the three relevant "
                        + "states.")),
                Paragraph(Text(
                    "Consequently no coordinate already present can be injective on all "
                        + "genotypes under this realization and context. The equality predicate "
                        + "of the first state supplies another readout that distinguishes the "
                        + "latent pair, making the dependence on observation language explicit."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula allele = F.Id("A");
        Formula contextType = F.Id("C");
        Formula state = F.Id("X");
        Formula indexType = F.Id("I");
        Formula output = F.Id("O");
        Formula realization = F.Id("realization");
        Formula readout = F.Id("q");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula context = F.Id("c");
        Formula i = F.Id("i");
        Formula genotypeVariable = F.Id("g");
        Formula distinguishingReadout = F.Id("d");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula genotype = Call("Sym2", allele);
        Formula profile = Call("jointReadout", readout);

        Formula Genotype(Formula first, Formula second) =>
            Call("s", first, second);

        Formula StateAt(Formula first, Formula second) =>
            Call("realization", Genotype(first, second), context);

        Formula xaa = StateAt(a, a);
        Formula xab = StateAt(a, b);
        Formula xbb = StateAt(b, b);
        Formula relevantStates = Seq(
            OpenBrace, xaa, Comma, Sp, xab, Comma, Sp, xbb, CloseBrace);
        Formula genotypeReadout = Lambda(
            genotypeVariable,
            genotype,
            Call("q", i, Call("realization", genotypeVariable, context)));
        Formula noInjectiveCoordinate = Seq(
            Forall, Sp, i, Colon, Sp, indexType, Comma, Sp,
            Neg, Sp, Call("Injective", genotypeReadout));
        Formula separatingReadout = Seq(
            Exists, Sp, distinguishingReadout, Colon, Sp,
            Arrow(state, proposition), Comma, Sp,
            NotEqual(
                Call("d", xaa),
                Call("d", xab)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, allele, Comma, Sp, contextType, Comma, Sp,
                state, Comma, Sp, indexType, Colon, Sp, type, Comma),
            Seq(
                output, Colon, Sp, indexType, Sp, To, Sp, type, Comma),
            Seq(
                realization, Colon, Sp, genotype, Sp, To, Sp,
                contextType, Sp, To, Sp, state, Comma),
            Seq(
                readout, Colon, Sp, Open,
                Forall, Sp, i, Colon, Sp, indexType, Comma, Sp,
                state, Sp, To, Sp, new Formula.Subscript(output, i),
                Close, Comma),
            Seq(
                a, Comma, Sp, b, Colon, Sp, allele, Comma, Sp,
                context, Colon, Sp, contextType, Comma),
            Seq(
                Open,
                NotEqual(xaa, xab), Sp, Land, Sp,
                Equal(Call("jointReadout", readout, xaa),
                    Call("jointReadout", readout, xab)), Sp, Land, Sp,
                NotEqual(Call("jointReadout", readout, xab),
                    Call("jointReadout", readout, xbb)),
                Close, Sp, Rightarrow),
            Seq(
                Open,
                Neg, Sp, Call("InjOn", profile, relevantStates), Sp, Land, Sp,
                Open, noInjectiveCoordinate, Close, Sp, Land, Sp,
                separatingReadout,
                Close, Dot),
        ]));
    }

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
}
