using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class DependentFinitePrimeTimeTomographyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Refinement/DependentFinitePrimeTimeTomography."
            + "dependent_finite_prime_time_tomography";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete separation by a dependent observer family on a finite carrier has a finite index-time window.",
        H("Dependent Finite Prime-Time Tomography"),
        Blocks(Describe.Lean(
            DescribeId.Create("dependent-complete-separation-has-a-finite-window"),
            DeclarationHandle.Create(Declaration),
            H("Complete dependent separation has a finite window"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The complete observation is the canonical dependent joint readout on pairs "
                        + "of observer indices and natural-number times. Each coordinate applies "
                        + "the indexed readout after the corresponding iterate of the update.")),
                Paragraph(Text(
                    "Finite-state separation first yields finitely many separating index-time "
                        + "coordinates. Their index projection is a finite observer family, and "
                        + "their finite supremum is a common time horizon containing every "
                        + "selected coordinate."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula output = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula coordinate = F.Id("c");
        Formula index = F.Id("i");
        Formula time = F.Id("n");
        Formula state = F.Id("x");
        Formula selected = F.Id("J");
        Formula depth = F.Id("m");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula coordinateType = Seq(indexType, Sp, Times, Sp, naturals);
        Formula indexAt = Call("fst", coordinate);
        Formula timeAt = Call("snd", coordinate);
        Formula evolved = Call("iterate", update, timeAt, state);
        Formula coordinateReadout = Seq(
            Open, coordinate, Colon, Sp, coordinateType, Sp, Mapsto, Sp,
            Open, state, Sp, Mapsto, Sp, Call("q", indexAt, evolved), Close, Close);
        Formula completeReadout = Call("jointReadout", coordinateReadout);
        Formula windowCoordinates = Seq(
            OpenBrace, coordinate, Colon, Sp, coordinateType, Sp, Mid, Sp,
            indexAt, Sp, InMacro, Sp, selected, Sp, Land, Sp,
            timeAt, Sp, Leq, Sp, depth, CloseBrace);
        Formula windowReadout = Call("jointReadout", Seq(
            Open, coordinate, Colon, Sp, windowCoordinates, Sp, Mapsto, Sp,
            Open, state, Sp, Mapsto, Sp, Call("q", indexAt, evolved), Close, Close));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp, type, Comma, Sp,
                output, Colon, Sp, indexType, Sp, To, Sp, type, Comma),
            Seq(
                Call("Finite", stateType), Comma, Sp,
                update, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
                stateType, Sp, To, Sp, Call("O", index), Comma),
            Seq(
                Call("Injective", completeReadout), Sp, Rightarrow, Sp,
                Exists, Sp, selected, Colon, Sp, Call("Finset", indexType), Comma, Sp,
                depth, Colon, Sp, naturals, Comma),
            Seq(Call("Injective", windowReadout), Dot),
        ]));
    }
}
