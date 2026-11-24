using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class UnequalMassPortHeatResistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.";
    private static readonly LibraryNoteRef Kron = LibraryNoteRef.Create("D5/L/GraphInvariants/dorflerbullo2013kron");

    public DocumentDefinition Create()
    {
        Formula b = F.Id("b");
        Formula t = F.Id("t");
        Formula v = F.Id("v");
        Formula q = F.Id("Q");
        Formula w = Call("w", b);
        Formula plus = Call("w", Call("true"));
        Formula minus = Call("w", Call("false"));
        Formula port = F.D(0);
        Formula hidden = F.D(1);
        Formula transpose = new Formula.Power(q, F.Id("T"));
        Formula plusL = Call("L", plus);
        Formula minusL = Call("L", minus);
        Formula current = F.Seq(F.Open, F.D(1), F.Comma, new Formula.Negate(F.D(1)), F.Comma,
            F.D(0), F.Close);
        Formula grounded = Logic(Eq(Product(Call("K", w), v), current),
            FormulaLogicOperator.And, Eq(Call("v", hidden), F.D(0)));
        Formula certificate = All("b", Call("Bool"), And(
            Eq(Call("R", w, port, hidden), Call("r", b)),
            Call("PositiveWeights", w),
            Eq(transpose, q),
            Eq(Product(q, q), Call("I")),
            Eq(Product(q, F.Id("z")), F.Id("z")),
            Eq(Product(q, Call("e", port)), Call("e", port)),
            Eq(minusL, Product(q, plusL, transpose)),
            All("t", Call("Real"), Eq(Call("H", plus, t, port, port), Call("H", minus, t, port, port))),
            Call("HasDerivAt", Call("cross", w), Call("s", b), port),
            All("v", Call("Voltage"), Logic(grounded, FormulaLogicOperator.Iff, Eq(v, Call("g", b))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Positive triangles of known unequal masses have equal full port heat and distinct hidden responses.",
            H("One-port heat on unequal-mass triangles"),
            Blocks(
                Paragraph(Text("The triangle construction and resistance comparison are from Sections 4 and 8 of Positive complete networks with the same port heat. Its labels 1, 2 and 3 correspond to 0, 1 and 2 here.")),
                Definition("matrix", "Mat", "Matrix space", "Real matrices on the three vertex labels 0, 1 and 2."),
                Definition("weights", "Weights", "Conductance space", "A real value on each unordered vertex pair."),
                Definition("triangle", "triangle", "Complete triangle", "The complete graph on 0, 1 and 2, with port 0 and hidden vertices 1 and 2."),
                Definition("mass", "rootMass", "Mass square roots", "The vector z = (1, 1, 2) gives the positive square roots of the masses (1, 1, 4)."),
                Definition("inverse-mass", "inverseRootMass", "Inverse square root of mass", "The diagonal matrix J has entries 1, 1 and 1/2."),
                Definition("stiffness", "stiffness", "Physical stiffness", "The matrix K(w) has the sum of incident conductances on the diagonal and the negative conductance off the diagonal."),
                Definition("normalization", "normalized", "Mass-normalized stiffness", "The matrix L(w) = JK(w)J governs the heat flow in mass-normalized coordinates."),
                Definition("heat", "physicalHeat", "Physical impulse response", "For time t ≥ 0, the entry H(w,t,i,j) of J exp(−tL(w)) J gives the temperature at i per unit impulse at j. The matrix exponential extends the formula to all real t. The function cross(w) is this response from input 0 to output 1."),
                Definition("positive", "PositiveWeights", "Positive conductances", "Every edge of the complete triangle has strictly positive conductance."),
                Definition("conductances", "conductances", "Two positive conductance assignments", "In edge order 01, 02, 12, the vector w(true) is (4/15, 17/30, 91/150) and w(false) is (1/15, 23/30, 109/150)."),
                Definition("reflection", "reflection", "Reflection", "Q has rows (1, 0, 0), (0, −3/5, 4/5), and (0, 4/5, 3/5)."),
                Definition("grounded-voltage", "groundedPotential", "Grounded unit-current potential", "The voltage g(true) is (352/197, 0, 170/197) and g(false) is (448/197, 0, 230/197). Both use vertex 1 as the ground."),
                Definition("claim", "claim", "Identification from the port curve", "For every pair of positive conductance assignments on the triangle with the prescribed masses, equality of their port curves for all real times would force equality of their hidden curves for all real times or equality of their resistances from 0 to 1."),
                Describe.Lean(DescribeId.Create("unequal-mass-triangle-certificate"),
                    DeclarationHandle.Create(Prefix + "triangle_certificate"),
                    H("Exact certificate for the two triangles"),
                    StatementSource.FromAuthor(F.Disp(certificate)), AssessedProvenance.FromRepo(Kron),
                    Blocks(
                        Paragraph(Text("The symmetric involution Q fixes the port vector and the mass square roots. Conjugation by Q takes the plus normalized stiffness to the minus one. Matrix exponentiation respects this conjugation at every real time, so the physical port entries coincide.")),
                        Paragraph(Text("The initial derivatives s(true) = 4/15 and s(false) = 1/15 follow from the derivative of the matrix exponential at zero. For every voltage vector v, the unit-current equations with vertex 1 grounded hold exactly when v is the displayed g(b). The native effective resistance R is the reciprocal of the current at 0 for the unique unit-voltage harmonic extension. Direct solution gives r(true) = 352/197 and r(false) = 448/197, the same voltage drops as in the unit-current solutions."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("unequal-mass-triangle-result"),
                    DeclarationHandle.Create(Prefix + "result"),
                    H("Refutation of hidden-response identification"),
                    StatementSource.FromAuthor(F.Disp(new Formula.Not(Call("claim")))),
                    AssessedProvenance.FromRepo(Kron),
                    Blocks(Paragraph(Text("The common port curve belongs to both actual networks. Their right derivatives at zero from 0 to 1 differ by 1/5, so their hidden curves differ at positive times. Their effective resistances from 0 to 1 differ by −96/197 in plus-minus order."))),
                    DescribeRole.Theorem))));
    }

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("unequal-mass-triangle-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? F.Seq(F.Operatorname, F.Grp(F.Id(name))) :
            new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(name))), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);

    private static Formula And(params Formula[] clauses) =>
        clauses.Reverse().Aggregate((right, left) => Logic(left, FormulaLogicOperator.And, right));

    private static Formula Product(params Formula[] factors) =>
        factors.Aggregate((left, right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right));
}
