using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FixedAlgebra;

internal sealed class SingletonRecordClassicalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singleton environment-record classes leave exactly a diagonal classical algebra.",
        H("Singleton Record Classicality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-record-classes-give-classical-fixed-algebra"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality."
                        + "singleton_record_classicality"),
                H("Singleton record classes give a classical fixed algebra"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite system and environment address sets, construct the record "
                            + "Gram overlap from normalized environment amplitudes and let the "
                            + "reduced channel multiply each matrix entry by that overlap. "
                            + "Assume unit overlap occurs only on the same address, so every "
                            + "record equivalence class is a singleton.")),
                    Paragraph(Text(
                        "The fixed matrices are exactly the diagonal matrices. The canonical "
                            + "diagonal algebra map has a range isomorphic to the coordinate "
                            + "algebra of complex functions on the system addresses, and its "
                            + "coordinates are recovered by diagonal entries; this range is "
                            + "commutative and is the stable accessible algebra.")),
                    Paragraph(Text(
                        "Finally, a positive trace-one fixed matrix has real nonnegative "
                            + "diagonal coordinates whose sum is one. Thus the observer state "
                            + "is exactly a probability vector."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula NormSquared(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert, Caret, Grp(D(2)));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula e = F.Id("e");
        Formula record = F.Id("E");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula a = F.Id("a");
        Formula rho = F.Id("rho");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula system = Call("Fin", d);
        Formula environment = Call("Fin", e);
        Formula matrix = Call("Matrix", system, system, complex);
        Formula gram = Call("recordGram", record, i, j);
        Formula channel = Call("recordChannel", record, rho);
        Formula diagonal = Call("diagonal", p);
        Formula diagonalRange = Call("range", Call("diagonalAlgHom", complex));
        Formula normalization = Seq(
            Forall, Sp, i, Colon, Sp, system, Comma, Sp,
            Sum, Underscore, Grp(a), Sp, InMacro, Sp, environment, Sp,
            NormSquared(Apply(record, i, a)), Sp, Eq, Sp, D(1));
        Formula separation = Seq(
            Forall, Sp, i, Comma, Sp, j, Colon, Sp, system, Comma, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            gram, Sp, Neq, Sp, D(1));
        Formula classLaw = Seq(
            Forall, Sp, i, Comma, Sp, j, Colon, Sp, system, Comma, Sp,
            gram, Sp, Eq, Sp, D(1), Sp, Leftrightarrow, Sp, i, Sp, Eq, Sp, j);
        Formula fixedLaw = Seq(
            Forall, Sp, rho, Colon, Sp, matrix, Comma, Sp,
            channel, Sp, Eq, Sp, rho, Sp, Leftrightarrow, Sp,
            rho, Sp, InMacro, Sp, diagonalRange);
        Formula diagonalLaw = Seq(
            Forall, Sp, p, Colon, Sp, system, To, complex, Comma, Sp,
            Call("recordChannel", record, Call("diagonal", p)), Sp, Eq,
            Call("diagonal", p), Sp, Land, Sp,
            Call("diagonalRangeEquiv", d), Open, Call("diagonal", p), Close,
            Sp, Eq, Sp, p);
        Formula commutativeLaw = Seq(
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp,
            diagonalRange, Comma, Sp,
            F.Id("x"), F.Id("y"), Sp, Eq, Sp, F.Id("y"), F.Id("x"));
        Formula probabilityLaw = Seq(
            Forall, Sp, rho, Colon, Sp, matrix, Comma, Sp,
            Call("PosSemidef", rho), Sp, Rightarrow, Sp,
            Call("trace", rho), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            channel, Sp, Eq, Sp, rho, Sp, Rightarrow, Sp,
            Exists, Sp, q, Colon, Sp, system, To, real, Comma, Sp,
            rho, Sp, Eq, Sp, Call("diagonal", q), Sp, Land, Sp,
            Forall, Sp, i, Colon, Sp, system, Comma, Sp, D(0), Sp, Le, Sp, Apply(q, i),
            Sp, Land, Sp, Sum, Underscore, Grp(i), Sp, InMacro, Sp, system, Sp,
            Apply(q, i), Sp, Eq, Sp, D(1));

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, e, Colon, Sp, F.Id("Nat"), Comma, Sp,
            record, Colon, Sp, system, To, environment, To, complex, Sp, Rightarrow,
            Open, normalization, Sp, Land, Sp, separation, Sp, Rightarrow, RowBreak, Grp(),
            Open, classLaw, Close, Sp, Land, Sp,
            Open, fixedLaw, Close, Sp, Land, Sp,
            Open, diagonalLaw, Close, Sp, Land, Sp,
            Open, commutativeLaw, Close, Sp, Land, Sp,
            Open, probabilityLaw, Close, Dot));
    }
}
