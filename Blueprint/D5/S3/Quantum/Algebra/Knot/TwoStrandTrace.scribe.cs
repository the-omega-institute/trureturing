using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class TwoStrandTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every signed power of the two-strand Artin generator has an exact weighted path-trace value.",
        H("Exact Trace of Signed Two-Strand Braids"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-strand-trace"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/TwoStrandTrace.two_strand_trace"),
            H("All integer crossing exponents"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let L be any finite decidable vertex type, R a decidable symmetric relation, d strictly positive real weights, and delta strictly positive with the exact Perron equality at every vertex. Fix any start s and nonzero complex A satisfying delta = -A squared minus A inverse squared. twoStrand(m) is the m-th integer power of the sole generator in the repository's actual two-strand Artin presentation. Empty endpoint fibers are retained. The theorem applies to every integer m, including zero and negative values.")),
                Paragraph(Text("Write P for the existing lastProjection on the two-edge path space. The actual represented generator is A inverse times (1-P) plus -A cubed times P. Its inverse has the reciprocal two coefficients. Idempotence gives two orthogonal algebraic sectors P and 1-P, so their coefficients multiply independently. Integer induction through the actual unit and its inverse yields the signed-power formula. No diagonalization, nonempty matrix block or extra matrix-inverse assumption is used.")),
                Paragraph(Text("The existing Perron Markov law gives tau(P) = delta inverse squared and tau(1) = 1. Combining these with the two-sector formula and the exact integer writhe m proves the displayed value. This supplies a concrete evaluation interface downstream of the existing representation and Markov descent. It computes every two-strand torus word and its mirror directly from scalar powers.")),
                Paragraph(Text("The mathematics is classical Temperley-Lieb and Jones theory. The crossing and writhe convention is the one already fixed by WeightedPathArtinRepresentation and its Aharonov-Jones-Landau source record, Library/Topology/aharonovjoneslandau2005jones.md. The result evaluates the formal algebraic Markov invariant. A geometric closure map and convention-preserving Jones identification remain separate obligations. This theorem does not construct the Aiello-Baader-Ferretti modulo-three witness or solve their Question 1.")),
                Paragraph(Text("The four-slot audit is unfinished. Its Reg mirror carries compiled actual-law, variation, sensitivity and dependence proofs, but the current source binding reports IE-C050 source.dictionary_or_proof_coordinate. The exact original theorem telescope and failed binding evidence are tracked in https://github.com/the-omega-institute/trureturing/issues/16285. This is an unresolved registration, not a validated source correspondence."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Statement()
    {
        Formula a = F.Id("A"), delta = F.Id("delta"), m = F.Id("m");
        Formula inv(Formula x) => Call("Inv", x);
        Formula pow(Formula x, Formula y) => Call("Pow", x, y);
        Formula k = Seq(Minus, pow(a, D(3)));
        Formula lambda = pow(inv(delta), D(2));
        Formula rhs = Seq(delta, Thin, pow(k, m), Thin,
            Open, pow(inv(a), m), Thin, Open, D(1), Minus, lambda, Close,
            Plus, pow(k, m), Thin, lambda, Close);
        Formula lhs = Call("F", Call("twoStrand", m));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Call("FiniteSymmetricPositivePerronData", F.Id("L"), F.Id("R"), F.Id("d"), delta),
            Semi, Sp, Call("Nonzero", a), Semi, Sp,
            new Formula.Relation(delta, FormulaRelationOperator.Equal,
                Seq(Minus, pow(a, D(2)), Minus, pow(inv(a), D(2)))), RowBreak,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("s"), F.Id("L"),
                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("m"),
                    F.Id("Z"), new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs))),
            End, Grp(F.Id("gathered"))));
    }
}
