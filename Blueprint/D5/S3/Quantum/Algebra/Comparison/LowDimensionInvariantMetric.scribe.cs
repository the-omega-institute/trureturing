using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class LowDimensionInvariantMetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/Comparison/LowDimensionInvariantMetric.";
    private static LibraryNoteRef Milnor => LibraryNoteRef.Create("D5/L/LieTheory/milnor1976curvatures");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A left-separating invariant bilinear form makes every Lie algebra of dimension at most two abelian, and an invariant form that is positive on nonzero vectors gives every non-abelian real Lie algebra of dimension three a basis, orthonormal for the form, in which the bracket is a positive multiple of the cross product.",
        H("Lie Algebras with an Invariant Form in Dimension at Most Three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("low-dimension-invariant-metric-abelian-le-two"),
                DeclarationHandle.Create(Prefix + "isLieAbelian_of_finrank_le_two"),
                H("Dimension at most two"),
                StatementSource.FromAuthor(AbelianFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let K be a field and L a finite-dimensional Lie algebra over K. The form written B in the displayed formula is a K-bilinear form on L. It is invariant, lieInvariant(B, L), when B([x,y], z) = -B(y, [x,z]) for all x, y, z in L; no symmetry of B is assumed. It is left separating, SeparatingLeft(B), when the only x with B(x, z) = 0 for every z is x = 0. If moreover finrank(K, L) is at most two, then L is abelian: [x, y] = 0 for all x and y.")),
                    Paragraph(Text("Invariance makes a bracket orthogonal to its arguments in the left slot: B([x,y], x) = -B(y, [x,x]) = 0, and B([x,y], y) = -B([y,x], y) = B(x, [y,y]) = 0. Suppose [x, y] is nonzero. Then x is nonzero, and x, y are linearly independent: applying [x, -] to s x + t y = 0 gives t [x, y] = 0, so t = 0 and then s = 0. Two independent vectors in a space of dimension at most two span it, so the linear functional B([x,y], -) vanishes on all of L, and left separation forces [x, y] = 0, a contradiction.")),
                    Paragraph(Text("No hypothesis can be dropped. On the two-dimensional non-abelian Lie algebra with basis e, f and [e, f] = f, the zero form is invariant, and over a field of characteristic other than two every invariant form vanishes on f in the left slot: B(f, e) = B([e,f], e) = -B(f, [e,e]) = 0 and B(f, f) = B([e,f], f) = -B(f, [e,f]) = -B(f, f). The standard dot product of the coordinates is left separating but not invariant. Finite dimension is needed because finrank is zero for infinite-dimensional spaces: the cross-product algebra on three-space plus an infinite-dimensional abelian summand, with the dot product on the first summand and any inner product on the second, is a non-abelian example."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-dimension-invariant-metric-cross-three"),
                DeclarationHandle.Create(Prefix + "exists_basis_bracket_eq_smul_cross"),
                H("Dimension three: the cross product"),
                StatementSource.FromAuthor(CrossFormula()),
                AssessedProvenance.FromRepo(Milnor),
                Blocks(
                    Paragraph(Text("Let L be a real Lie algebra of dimension three that is not abelian, and B an invariant real bilinear form on L with B(x, x) > 0 for every nonzero x; B is not assumed symmetric. Then there are a basis b of L indexed by Fin 3 and a real number c > 0 such that B(b(i), b(j)) is 1 for i = j and 0 otherwise, and such that for all x and y the coordinate vector of [x, y] in the basis b, written equivFun(b)([x, y]), is c times the cross product of the coordinate vectors of x and y. Evaluating at basis vectors gives [b(0), b(1)] = c b(2), [b(1), b(2)] = c b(0) and [b(2), b(0)] = c b(1). Since B is the identity matrix in the basis b, the conclusion also shows that B is symmetric.")),
                    Paragraph(Text("Choose x, y with [x, y] nonzero. Invariance gives B([x,[x,y]], y) = -B([x,y], [x,y]) < 0, so [x, [x, y]] is nonzero as well. Rescale x and [x, y] to vectors e1, e2 of square one; they are orthogonal in both slots because a bracket is orthogonal to its arguments. Their bracket is a positive multiple of a unit vector e3, which is again orthogonal to e1 and e2 in both slots. Three orthonormal vectors are linearly independent and so form a basis, in which the coordinates of z are B(z, e1), B(z, e2), B(z, e3). Invariance then determines the remaining brackets: B([e2,e3], e1) = -B(e3, [e2,e1]) gives [e2, e3] = c e1, and similarly [e3, e1] = c e2. Both sides of the claimed identity are bilinear in x and y and agree on the basis.")),
                    Paragraph(Text("The cross-product algebra on three-space with the dot product satisfies all hypotheses, with the standard basis and c = 1. Positivity cannot be weakened to non-degeneracy: on sl(2, R) the Killing form is invariant and non-degenerate but not positive, while the conclusion forces the form to be positive. The zero form on the cross-product algebra is invariant and fails the conclusion, so the form must be positive and not merely invariant. The non-abelian hypothesis is needed, since three-space with the zero bracket and the dot product satisfies the other hypotheses and has no such basis.")),
                    Paragraph(Text("Related statements hold under further hypotheses: "),
                        Ref("D5/S3/Quantum/Algebra/RankOneInvariantMetric.min_frame"),
                        Text(" gives a frame of this kind and "),
                        Ref("D5/S3/Quantum/Algebra/RankOneInvariantMetric.finrank_eq_one_or_three"),
                        Text(" the dimension count, both assuming that the centralizer of a fixed element is a line, and the last clause of "),
                        Ref("D5/S3/Quantum/Algebra/Comparison/RoundTripClassification.comparison_classification"),
                        Text(" gives an orthonormal frame of the same kind under the round-trip comparison hypotheses. The present statement assumes neither and uses only invariance, positivity, dimension three and non-commutativity."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Instance(Formula cls) => Seq(OpenBracket, cls, CloseBracket, Comma, Esc);
    private static Formula Bracket(Formula x, Formula y) => Seq(OpenBracket, x, Comma, Sp, y, CloseBracket);
    private static Formula Word(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula AbelianFormula()
    {
        Formula k = F.Id("K"), l = F.Id("L"), b = F.Id("B");
        Formula body = ForAll("B", Call("BilinForm", k, l),
            Implies(Call("lieInvariant", b, l),
                Implies(Call("SeparatingLeft", b),
                    Implies(Rel(Call("finrank", k, l), FormulaRelationOperator.LessThanOrEqual, D(2)),
                        Call("IsLieAbelian", l)))));
        return Disp(ForAll("K", TypeStar, ForAll("L", TypeStar, Seq(
            Instance(Call("Field", k)),
            Instance(Call("LieRing", l)),
            Instance(Call("LieAlgebra", k, l)),
            Instance(Call("FiniteDimensional", k, l)),
            body))));
    }

    private static Formula CrossFormula()
    {
        Formula l = F.Id("L"), b = F.Id("B"), x = F.Id("x"), y = F.Id("y");
        Formula basis = F.Id("b"), c = F.Id("c"), i = F.Id("i"), j = F.Id("j");
        Formula fin3 = Call("Fin", D(3));
        Formula coords = Call("equivFun", basis);
        Formula ite = Seq(Word("if"), Sp, i, Eq, j, Sp, Word("then"), Sp, D(1), Sp, Word("else"), Sp, D(0));
        Formula orthonormal = ForAllMany(fin3,
            Equal(At(b, At(basis, i), At(basis, j)), ite), "i", "j");
        Formula cross = ForAllMany(l,
            Equal(At(coords, Bracket(x, y)),
                new Formula.Binary(c, FormulaBinaryOperator.Multiply,
                    Call("crossProduct", At(coords, x), At(coords, y)))), "x", "y");
        Formula conclusion = Exists("b", Call("Basis", fin3, Reals, l), Exists("c", Reals,
            And(Rel(D(0), FormulaRelationOperator.LessThan, c), And(orthonormal, cross))));
        Formula positive = ForAll("x", l,
            Implies(Rel(x, FormulaRelationOperator.NotEqual, D(0)),
                Rel(D(0), FormulaRelationOperator.LessThan, At(b, x, x))));
        Formula body = ForAll("B", Call("BilinForm", Reals, l),
            Implies(Call("lieInvariant", b, l),
                Implies(positive,
                    Implies(Equal(Call("finrank", Reals, l), D(3)),
                        Implies(new Formula.Not(Call("IsLieAbelian", l)), conclusion)))));
        return Disp(ForAll("L", TypeStar, Seq(
            Instance(Call("LieRing", l)),
            Instance(Call("LieAlgebra", Reals, l)),
            body)));
    }
}
