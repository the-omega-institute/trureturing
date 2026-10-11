using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class EclecticTwoWallUniversalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ahn2022eclectic");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("k");
    private static Formula Xi => F.Id("xi");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Length => PlusOf(PlusOf(A, B), D(2));
    private static Formula Classes => Call("Fin", Length);
    private static Formula Couplings => new Formula.TypeArrow(Call("Fin", D(3)), Complexes);
    private static Formula Eigenvalue => Call("eigenvalue", A, B, K);
    private static Formula Sector => Call("sector", A, B, K);
    private static Formula X0 => Seq(Bang, OpenBracket, D(0), Comma, Sp, D(0), Comma, Sp, D(1), CloseBracket);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every two-wall cyclicity class has maximal hypereclectic power ranks, attained generically by the eclectic operator.",
        H("Two-wall universality of Jordan block spectra"),
        Blocks([
            Paragraph(Text("Work over the complex numbers. A filling contains a letters 1, b letters 2 and two walls 3, so L = a+b+2. Cyclicity indices k range over Fin(L), with val(k) in {0,...,L−1}. The space retains literal periodic words; its cyclicity class is the eigenspace of the one-site right shift. The three coupling coordinates xi(0), xi(1), xi(2) multiply F1, F2, F3, respectively. Thus ![0,0,1] is the hypereclectic point with coefficient one on F3.")),
            Node("eigenvalue", "Cyclicity eigenvalue", ABK(Eq(Eigenvalue,
                Call("Complex.exp", new Formula.Fraction(Mul(Mul(Mul(D(2), Call("cast", F.Pi, Complexes)), Call("Complex.I")),
                    Call("cast", Call("val", K), Complexes)), Call("cast", Length, Complexes))))), true,
                "Complex.I is the imaginary unit. Natural and real scalars in this expression are cast into the complex numbers."),
            Node("sector", "The cyclicity class", ABK(Eq(Sector,
                Call("eigenspace", Call("U", Complexes, A, B), Eigenvalue))), true,
                "This is a complex submodule of Space(C,a,b), including the possibility of a zero-dimensional eigenspace."),
            Node("sectorF", "Restricted bond operators", ABK(All("j", Call("Fin", D(3)),
                Eq(Call("sectorF", A, B, K, F.Id("j")),
                    Call("restrict", Call("F", Complexes, A, B, F.Id("j")), Sector)))), true,
                "Each bond sum commutes with U and therefore preserves the eigenspace. The index 2 selects F3, the literal 21 to 12 bond sum."),
            Node("sectorT", "The restricted eclectic operator", ABK(All("xi", Couplings,
                Eq(Call("sectorT", A, B, K, Xi),
                    Call("restrict", Call("T", Complexes, A, B, Xi), Sector)))), true,
                "The coupled operator also commutes with U. Its restriction is the same linear combination of the three restricted bond sums."),
            Node("claim", "Universality for every filling with a,b at least two",
                Iff(Call("claim"), Universality()), true,
                "§5, Eq. (5.1), arXiv:2112.04506v1: \"However, we claim a universality hypothesis: The Jordan block spectrum of the eclectic model for generic couplings ξ1, ξ2, ξ3 is identical to that of the hypereclectic model, provided L, M, K satisfy L1 = L−M ≥ K, M1 = M−K ≥ K. (5.1)\" Here K = 2, L = a+b+2 and M = b+2, so the two inequalities become a,b at least two. All couplings satisfy the power-rank upper bound. A single polynomial for the filling certifies equality of every power rank and every Jordan block multiplicity in every cyclicity class. Both restricted operators are nilpotent and admit positive-length chain bases; these bases are their Jordan block decompositions. The multiplicity equality holds for every pair of such bases. The basis index is the dependent sum of Fin(val(s(i))), and the conditional basis entry is used only when the new position is below s(i). Normalization at the hypereclectic point implies that this polynomial is nonzero."),
            ..CertificateContent(),
            Node("result", "The two-wall universality theorem", Universality(), false,
                "The literal two-wall sl2 action has lowering operator F3 and commutes with the shift. Its integral weight decomposition restricts to every cyclicity class. When a,b are at least two, each term of T lowers the weight filtration by at least two, so the eigenspace rank comparison gives the upper bound for every coupling and every power. Choose any complex basis of each class and express the three restricted bond sums as matrices. The matrix with entries X0 C(A1(i,j)) + X1 C(A2(i,j)) + X2 C(A3(i,j)) evaluates to the matrix of the restricted T. At ![0,0,1] it is the matrix of F3. Matrix rank equals the dimension of the operator range, and the basis map preserves powers. The weight bound gives F3^(ab+1) = 0, also on each restricted space. The polynomial power-rank certificate with this cutoff therefore supplies a polynomial for each class, normalized to one at the hypereclectic point. Their finite product over Fin(L) has the same normalization, and a nonzero product makes every factor nonzero, giving all equalities simultaneously. Empty bases and zero ranks are included. The weight filtration also makes T^(ab+1) zero, so both restricted operators are nilpotent. The nilpotent chain theorem supplies their Jordan block decompositions. For any such basis with lengths s(i), the rank of the m-th power is the sum of the truncated differences val(s(i))−m. For each positive j, the integer second difference rho(j-1) - 2 rho(j) + rho(j+1) counts chains of length j. Thus equality of all power ranks gives equality of all Jordan block multiplicities, independently of either choice of chain basis. At j=0 both counts vanish because every chain length is positive.")]),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose) =>
        Describe.Lean(DescribeId.Create("eclectic-two-wall-universality-" + name.ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            name is "claim" or "result" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args)
    {
        var symbol = Seq(Operatorname, Grp(name.Split('.').SelectMany((part, i) =>
            i == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray()));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Pair(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, Sp, y, Rangle);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula PlusOf(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula AB(Formula body) => All("a", Nats, All("b", Nats, body));
    private static Formula ABK(Formula body) => AB(All("k", Classes, body));
    private static Formula Rank(Formula op) => Call("finrank", Complexes,
        Call("range", new Formula.Power(Parenthesized(op), F.Id("r"))));
    private static Formula ChainAction(Formula op, string indexName, string lengthName, string basisName)
    {
        var i = F.Id("i");
        var t = F.Id("t");
        var m = F.Id("m");
        var size = Call("val", At(F.Id(lengthName), i));
        var next = PlusOf(Call("val", t), m);
        return All("m", Nats, All("i", F.Id(indexName), All("t", Call("Fin", size),
            Eq(At(new Formula.Power(Parenthesized(op), m), At(F.Id(basisName), Pair(i, t))),
                Call("ite", new Formula.Relation(next, FormulaRelationOperator.LessThan, size),
                    At(F.Id(basisName), Pair(i, Parenthesized(Seq(Call("Fin.mk", next), Sp, Colon, Sp, Call("Fin", size))))), D(0))))));
    }
    private static Formula ChainBasisType(string indexName, string lengthName) =>
        Call("Basis", Parenthesized(Seq(Sigma, Sp,
            Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id(indexName))), Comma, Sp,
            Call("Fin", Call("val", At(F.Id(lengthName), F.Id("i")))))), Complexes, Sector);
    private static Formula ChainsExist(Formula op, string indexName, string lengthName, string basisName) =>
        Some(indexName, F.Id("Type"),
            Assumption(Call("Fintype", F.Id(indexName)),
                Some(lengthName, new Formula.TypeArrow(F.Id(indexName), Call("PNat")),
                    Some(basisName, ChainBasisType(indexName, lengthName),
                        ChainAction(op, indexName, lengthName, basisName)))));
    private static Formula BlockCount(string indexName, string lengthName) =>
        Call("card", new Formula.SetBuilder(F.Id("i"), F.Id("i"),
            Seq(F.Id(indexName), Sp, Land, Sp, Eq(Call("val", At(F.Id(lengthName), F.Id("i"))), F.Id("j")))));
    private static Formula EqualBlockCounts(Formula top, Formula fop)
    {
        var counts = All("j", Nats, Eq(BlockCount("I", "s"), BlockCount("J", "q")));
        var shifts = Implies(ChainAction(top, "I", "s", "bt"),
            Implies(ChainAction(fop, "J", "q", "bf"), counts));
        var bases = All("bt", ChainBasisType("I", "s"), All("bf", ChainBasisType("J", "q"), shifts));
        var sizes = All("s", new Formula.TypeArrow(F.Id("I"), Call("PNat")),
            All("q", new Formula.TypeArrow(F.Id("J"), Call("PNat")), bases));
        return All("I", F.Id("Type"), All("J", F.Id("Type"),
            Assumption(Call("Fintype", F.Id("I")), Assumption(Call("Fintype", F.Id("J")), sizes))));
    }
    private static Formula Universality()
    {
        var top = Call("sectorT", A, B, K, Xi);
        var fop = Call("sectorF", A, B, K, D(2));
        var t = Rank(top);
        var f = Rank(fop);
        var upper = All("xi", Couplings, All("k", Classes, All("r", Nats, Le(t, f))));
        var p = F.Id("P");
        var jordan = And(All("r", Nats, Eq(t, f)),
            And(Call("IsNilpotent", top), And(Call("IsNilpotent", fop),
                And(ChainsExist(top, "I", "s", "bt"),
                    And(ChainsExist(fop, "J", "q", "bf"), EqualBlockCounts(top, fop))))));
        var generic = Some("P", Call("MvPolynomial", Call("Fin", D(3)), Complexes),
            And(Eq(Call("eval", X0, p), D(1)), All("xi", Couplings,
                Implies(Ne(Call("eval", Xi, p), D(0)), All("k", Classes, jordan)))));
        return AB(Implies(Le(D(2), A), Implies(Le(D(2), B), And(upper, generic))));
    }

    private static DocumentBlock[] CertificateContent() => [
            Paragraph(Text("Let K be any field, I a finite matrix index type with decidable equality, and S any type of variables. For a polynomial matrix A and a point x : S → K, write A(x) for the matrix obtained by evaluating every entry at x. No characteristic assumption or finiteness assumption on S is needed.")),
            Describe.Lean(
                DescribeId.Create("polynomial-power-ranks-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.exists_polynomial_power_rank_certificate"),
                H("One polynomial certifies all powers"),
                StatementSource.FromAuthor(Disp(CertificateStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose the specialization at z is nilpotent with cutoff H and dominates the rank of every power at every point. There is a polynomial P whose value at z is one. At every point where P is nonzero, all power ranks agree with their values at z.")),
                    Paragraph(Text("For each r below H, put d equal to the rank of A(z) raised to r. Choose constant left and right matrices taking this power to rank normal form, with an identity block of size d. Lift their entries to constant polynomials and take the determinant of the corresponding block of the transformed polynomial power. Evaluation commutes with multiplication, powers, and determinants, so this determinant evaluates to one at z. A nonzero value gives a full-rank block, and the submatrix and product rank inequalities force rank at least d.")),
                    Paragraph(Text("The finite product of these determinants is P. Its value at z is one, and a nonzero product forces every factor to be nonzero. The assumed rank bound supplies the opposite inequality. For powers at least H, nilpotence makes the reference power zero, and the same bound forces rank zero at every point. Empty blocks have determinant one, so zero ranks and empty matrix index types are included."))),
                DescribeRole.Theorem)];

    private static Formula CertificateAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? CertificateParenthesized(type) : type, body);
    private static Formula CertificateSome(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? CertificateParenthesized(type) : type, body);
    private static Formula CertificateCall(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula CertificateParenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula CertificateEq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula CertificateLe(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula CertificateNe(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula CertificateAnd(Formula x, Formula y) =>
        new Formula.Logic(CertificateParenthesized(x), FormulaLogicOperator.And, CertificateParenthesized(y));
    private static Formula CertificateImplies(Formula x, Formula y) =>
        new Formula.Logic(CertificateParenthesized(x), FormulaLogicOperator.Implies, CertificateParenthesized(y));
    private static Formula CertificateAssumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula CertificateArrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula CertificatePower(Formula x, Formula r) => new Formula.Power(CertificateParenthesized(x), r);

    private static Formula CertificateStatement()
    {
        var k = F.Id("K"); var i = F.Id("I"); var s = F.Id("S");
        var a = F.Id("A"); var z = F.Id("z"); var h = F.Id("H");
        var x = F.Id("x"); var r = F.Id("r"); var p = F.Id("P");
        var type = CertificateCall("Type");
        var nats = Seq(Mathbb, Grp(F.Id("N")));
        var polynomial = CertificateCall("MvPolynomial", s, k);
        var point = CertificateArrow(s, k);
        Formula MatrixAt(Formula t) => CertificateCall("map", a, CertificateCall("eval", t));
        Formula RankAt(Formula t) => CertificateCall("rank", CertificatePower(MatrixAt(t), r));
        var bounded = CertificateAll("x", point, CertificateAll("r", nats, CertificateLe(RankAt(x), RankAt(z))));
        var ranks = CertificateAll("r", nats, CertificateEq(RankAt(x), RankAt(z)));
        var locus = CertificateAll("x", point, CertificateImplies(CertificateNe(CertificateCall("eval", x, p), D(0)), ranks));
        var conclusion = CertificateSome("P", polynomial, CertificateAnd(CertificateEq(CertificateCall("eval", z, p), D(1)), locus));
        var claim = CertificateImplies(CertificateAnd(CertificateEq(CertificatePower(MatrixAt(z), h), D(0)), bounded), conclusion);
        var data = CertificateAll("A", CertificateCall("Matrix", i, i, polynomial), CertificateAll("z", point, CertificateAll("H", nats, claim)));
        var instances = CertificateAssumption(CertificateCall("Field", k),
            CertificateAssumption(CertificateCall("Fintype", i), CertificateAssumption(CertificateCall("DecidableEq", i), data)));
        return CertificateAll("K", type, CertificateAll("I", type, CertificateAll("S", type, instances)));
    }
}
