using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class A5TwelveCosetFiniteCertificateDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/A5TwelveCosetFiniteCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite twelve-point permutation certificate computes the A5 boundary counts.",
        H("Finite A5 twelve-coset certificate"),
        Blocks(
            Paragraph(Text(
                "This document records the concrete twelve-point input from the A5 noncommutative "
                    + "transport example. The two permutations are given both by their image tables "
                    + "and by disjoint cycle products. The return permutations use the displayed "
                    + "right-action convention through low squared times high inverse and low times "
                    + "high squared.")),
            Paragraph(Text(
                "The kernel computation certifies only this finite data: the two return cycle types, "
                    + "the four endpoint orbit counts, and the resulting (V,E,F)=(20,72,48), "
                    + "Euler characteristic -4, and genus 3. It does not formalize the general "
                    + "noncommutative face-transport theorem, A5 generation, or a geometric "
                    + "realization of every group action.")),
            Theorem("a5_finite_cycle_certificate", "finite-a5-cycle-certificate",
                "Finite A5 cycle and link certificate", CertificateFormula(),
                "The explicit Fin(12) table is checked pointwise by the kernel. The cycleType "
                    + "equalities are a bounded permutation computation, and the count definitions "
                    + "then evaluate to the stated link data."))));

    private static DocumentBlock Theorem(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
        StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Fin12() => Call("Fin", Number(12));
    private static Formula ImageTable(string name, Formula i) => Call(name, i);
    private static Formula CycleType(Formula p) => Call("cycleType", p);
    private static Formula Multiset(params int[] values)
    {
        var entries = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) entries.AddRange([Comma, Sp]);
            entries.Add(Number(values[i]));
        }
        return F.Seq([OpenBrace, .. entries, CloseBrace]);
    }

    private static Formula Number(int value) =>
        D(value.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(character => (byte)(character - '0')).ToArray());

    private static Formula CertificateFormula()
    {
        Formula i = F.Id("i");
        Formula low = F.Id("lowGenerator");
        Formula high = F.Id("highGenerator");
        Formula pointwise = And(
            All("i", Fin12(), Eq(Call("lowGenerator", i), ImageTable("lowImageTable", i))),
            All("i", Fin12(), Eq(Call("highGenerator", i), ImageTable("highImageTable", i))));
        Formula cycles = And(
            Eq(CycleType(low), Multiset(3, 3, 3, 3)),
            Eq(CycleType(high), Multiset(5, 5)),
            Eq(CycleType(Call("lowReturn")), Multiset(2, 2, 2, 2, 2, 2)),
            Eq(CycleType(Call("highReturn")), Multiset(3, 3, 3, 3)));
        Formula counts = And(
            Eq(Call("vertexCount"), Number(20)),
            Eq(Call("edgeCount"), Number(72)),
            Eq(Call("faceCount"), Number(48)),
            Eq(Call("eulerCharacteristic"), F.Seq(Minus, Sp, Number(4))),
            Eq(Call("boundaryGenus"), Number(3)));
        return And(pointwise, cycles, counts);
    }
}
