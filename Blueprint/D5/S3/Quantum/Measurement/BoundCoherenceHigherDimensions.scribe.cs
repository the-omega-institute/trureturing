using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class BoundCoherenceHigherDimensionsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/strattonhsiehskrzypczyk2026concentration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every dimension at least three admits a coherent, nonmaximal density matrix whose positive modes cannot increase under an allowed interaction of two identical copies.",
        H("Bound coherence in every dimension at least three"),
        Blocks(
            Definition("number-op", "numberOp", "The truncated number observable", NumberOpFormula(),
                "The number observable is diagonal in the number basis, with eigenvalues zero through d minus one. "
                    + "The natural value of each index is cast to a complex scalar. This is the local observable in Section II, main.tex line 224.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("allowed-unitary", "IsAllowedUnitary", "Interactions conserving total number", AllowedFormula(),
                "An allowed interaction is a unitary matrix on the product basis that commutes with the sum of the two local number observables. "
                    + "The two identity matrices act on the respective local systems. Section II, main.tex lines 219–224, gives this conservation condition.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("mode", "mode", "A signed number-difference mode", ModeFormula(),
                "The jth mode retains exactly those entries whose row number minus column number equals the integer j. "
                    + "Both natural index values are cast to integers before subtraction. Entries outside this diagonal are zero. "
                    + "This is the entrywise form of the mode in Section III, main.tex lines 230–232; the definition also applies to arbitrary matrices and arbitrary integer j.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("mode-coherence", "modeCoherence", "The trace norm of a mode", ModeCoherenceFormula(),
                "Coherence in mode j is the real trace norm of that mode. Section IV, main.tex lines 260–261, uses this quantity. "
                    + "The trace norm here is the real part of the trace of the positive square root of the conjugate transpose times the matrix; "
                    + "the source writes the equivalent square root of the matrix times its conjugate transpose.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("concentrated", "concentrated", "The first output marginal", ConcentratedFormula(),
                "Form the tensor product of two identical matrices, conjugate it by v, and trace out the second system. "
                    + "For a density matrix and an allowed unitary this is the first output state of the two-copy concentration experiment in Section IV, main.tex line 265. "
                    + "The definition itself imposes neither positivity nor unitarity.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("maximally-coherent", "IsMaximallyCoherent", "Equal-amplitude pure states", MaximalFormula(),
                "A maximally coherent matrix is the outer product of a vector with its conjugate, where every coordinate has modulus one over the square root of d. "
                    + "The real phase θ n is cast to a complex number before multiplication by the imaginary unit. "
                    + "The natural dimension is first cast to a real number for the square root, and that square root is then cast to a complex number. "
                    + "This specifies the general-dimensional meaning of maximal coherence used here.",
                AssessedProvenance.FromRepo(Source)),
            Definition("claim", "claim", "No positive mode can be concentrated", ClaimFormula(),
                "For every natural dimension d at least three, there is a positive semidefinite matrix of trace one that does not commute with the number observable "
                    + "and is not an equal-amplitude pure state. For every allowed unitary on two copies, each positive local mode from one through d minus one "
                    + "has output coherence at most its input coherence. This gives a precise reading of the higher-dimensional question in Section IX, main.tex line 387. "
                    + "The statement concerns two identical copies and the first marginal.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("bound-coherence-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Existence in all dimensions at least three"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix d at least three and put D = d − 1, z = 0 and l = D in the number basis. "
                            + "Take ρ to have every diagonal entry 1/d, the two entries ρ(l,z) = ρ(z,l) = 1/d, and all other entries zero. "
                            + "The indices z and l are distinct. First bound the output entry between l and z for an arbitrary allowed unitary v.")),
                    Paragraph(Text(
                        "The total number observable is diagonal on pairs a, with diagonal entry a₁ + a₂. "
                            + "Commutation therefore gives v(a,b) = 0 whenever a₁ + a₂ differs from b₁ + b₂. "
                            + "For a fixed k, the portion of ρ ⊗ ρ from total number k to total number D + k has only two possible entries: "
                            + "from (z,k) to (l,k), and from (k,z) to (k,l), each with coefficient 1/d². "
                            + "Expanding the conjugation and partial trace consequently gives the output entry "
                            + "q = d⁻² ∑ₖ t(k), where t(k) = v((l,k),(l,k)) conjugate(v((z,k),(z,k))) "
                            + "+ v((l,k),(k,l)) conjugate(v((z,k),(k,z))).")),
                    Paragraph(Text(
                        "If k is neither endpoint, the two selected columns in each of the rows (l,k) and (z,k) are distinct. "
                            + "The sums of the squared moduli of the two selected entries in each row are at most one, because v is unitary. "
                            + "The triangle inequality and Cauchy–Schwarz then give |t(k)| ≤ 1.")),
                    Paragraph(Text(
                        "At the endpoints the repeated entries must be combined. One has "
                            + "t(z) = (v((l,z),(l,z)) + v((l,z),(z,l))) conjugate(v((z,z),(z,z))) "
                            + "and t(l) = v((l,l),(l,l)) conjugate(v((z,l),(z,l)) + v((z,l),(l,z))). "
                            + "The columns indexed by (l,z) and (z,l) are orthonormal, so their sum has squared norm two. "
                            + "Thus the squared moduli of its coordinates at (l,z) and (z,l) sum to at most two. "
                            + "Each remaining diagonal factor has modulus at most one. Cauchy–Schwarz bounds the sum of the two selected moduli by two, "
                            + "and hence |t(z)| + |t(l)| ≤ 2.")),
                    Paragraph(Text(
                        "There are d − 2 interior indices. Splitting the sum into the interior and the two endpoints, "
                            + "the triangle inequality gives |∑ₖ t(k)| ≤ (d − 2) + 2 = d. "
                            + "Multiplying by d⁻² proves |q| ≤ 1/d.")),
                    Paragraph(Text(
                        "To verify positivity of ρ, let u have value one at z and l and zero elsewhere, "
                            + "and let f have value zero at those endpoints and one elsewhere. "
                            + "Then ρ = d⁻¹(uu† + diagonal(f)), a nonnegative real multiple of a sum of positive semidefinite matrices. "
                            + "Its d diagonal entries are 1/d, so its trace is one. The (l,z) entries of ρ times the number observable "
                            + "and of the number observable times ρ are respectively zero and D/d. Since D/d is nonzero, ρ is coherent. "
                            + "Its entry at (0,1) is zero, whereas every such entry of an equal-amplitude pure state is a product of two nonzero exponential amplitudes. "
                            + "The denominator square root is nonzero because d is positive. Thus ρ is not maximally coherent.")),
                    Paragraph(Text(
                        "For a natural j with 1 ≤ j < D, the tensor product has no entry with total number difference j: "
                            + "each factor has number differences only zero, D and −D, so a positive sum smaller than D is impossible. "
                            + "In an output entry of difference j, the conservation condition forces the intermediate tensor entry to have that same total difference; "
                            + "it is therefore zero. Summing over the traced index proves that every lower positive output mode vanishes.")),
                    Paragraph(Text(
                        "For any matrix x, its mode D consists of the single entry x(l,z). "
                            + "The conjugate transpose of this single-entry matrix times itself has the positive square root "
                            + "with sole entry |x(l,z)| at (z,z). Taking its trace shows that mode D has trace norm |x(l,z)|. "
                            + "For ρ this equals 1/d, and the bound on q proves the required comparison in mode D. "
                            + "For each smaller positive mode the output trace norm is zero and the input trace norm is nonnegative. "
                            + "These two cases cover every j from one through d minus one. Together with positivity, unit trace, coherence and nonmaximality, "
                            + "they establish the asserted existence for every d at least three."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("bound-coherence-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula NumberOpFormula() => All("d", Naturals(),
        Equal(Typed(LocalCall("numberOp", X("d")), LocalMatrix()),
            At(Qualified("Matrix", "diagonal"), LambdaOf("n", FinD(),
                NatCast(At(Qualified("Fin", "val"), X("n")), Complexes())))));

    private static Formula AllowedFormula()
    {
        Formula number = LocalCall("numberOp", X("d"));
        Formula identity = Typed(D(1), LocalMatrix());
        Formula total = Add(At(Qualified("Matrix", "kronecker"), number, identity),
            At(Qualified("Matrix", "kronecker"), identity, number));
        return All("d", Naturals(), All("v", ProductMatrix(),
            Equivalence(LocalCall("IsAllowedUnitary", X("v")),
                And(new Formula.Relation(X("v"), FormulaRelationOperator.MemberOf,
                        At(Qualified("Matrix", "unitaryGroup"), ProductIndex(), Complexes())),
                    Equal(Mul(X("v"), total), Mul(total, X("v")))))));
    }

    private static Formula ModeFormula() => All("d", Naturals(), All("j", Integers(),
        All("ρ", LocalMatrix(), Equal(Typed(LocalCall("mode", X("j"), Rho), LocalMatrix()),
            LambdaOf("r", FinD(), LambdaOf("s", FinD(),
                At(Qualified("ite"),
                    Equal(Subtract(NatCast(At(Qualified("Fin", "val"), X("r")), Integers()),
                        NatCast(At(Qualified("Fin", "val"), X("s")), Integers())), X("j")),
                    At(Rho, X("r"), X("s")), Typed(D(0), Complexes()))))))));

    private static Formula ModeCoherenceFormula() => All("d", Naturals(), All("j", Integers(),
        All("ρ", LocalMatrix(), Equal(Typed(LocalCall("modeCoherence", X("j"), Rho), Reals()),
            At(Qualified("D5", "S3", "Quantum", "Foundation", "FiniteTraceDistance", "traceNorm"),
                LocalCall("mode", X("j"), Rho))))));

    private static Formula ConcentratedFormula() => All("d", Naturals(), All("v", ProductMatrix(),
        All("ρ", LocalMatrix(), Equal(Typed(LocalCall("concentrated", X("v"), Rho), LocalMatrix()),
            At(Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "partialTraceRight"),
                Mul(Mul(X("v"), At(Qualified("Matrix", "kronecker"), Rho, Rho)),
                    At(Qualified("Matrix", "conjTranspose"), X("v"))))))));

    private static Formula MaximalFormula()
    {
        Formula amplitude = LambdaOf("n", FinD(),
            new Formula.Fraction(
                At(Qualified("Complex", "exp"), Mul(
                    At(Qualified("Complex", "ofReal"), At(Theta, X("n"))), Qualified("Complex", "I"))),
                At(Qualified("Complex", "ofReal"),
                    At(Qualified("Real", "sqrt"), NatCast(X("d"), Reals())))));
        return All("d", Naturals(), All("ρ", LocalMatrix(),
            Equivalence(LocalCall("IsMaximallyCoherent", Rho),
                Some("θ", Arrow(FinD(), Reals()), Equal(Rho,
                    At(Qualified("Matrix", "vecMulVec"), amplitude, At(Qualified("Star", "star"), amplitude)))))));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"), ClaimBody());

    private static Formula ClaimBody()
    {
        Formula comparison = LE(
            LocalCall("modeCoherence", NatCast(X("j"), Integers()), LocalCall("concentrated", X("v"), Rho)),
            LocalCall("modeCoherence", NatCast(X("j"), Integers()), Rho));
        Formula modes = All("v", ProductMatrix(), Imp(LocalCall("IsAllowedUnitary", X("v")),
            All("j", Naturals(), Imp(LE(D(1), X("j")),
                Imp(LE(X("j"), Subtract(X("d"), D(1))), comparison)))));
        Formula state = And(At(Qualified("Matrix", "PosSemidef"), Rho),
            And(Equal(At(Qualified("Matrix", "trace"), Rho), Typed(D(1), Complexes())),
                And(NotEqual(Mul(Rho, LocalCall("numberOp", X("d"))),
                        Mul(LocalCall("numberOp", X("d")), Rho)),
                    And(new Formula.Not(Parenthesized(LocalCall("IsMaximallyCoherent", Rho))), modes))));
        return All("d", Naturals(), Imp(LE(D(3), X("d")), Some("ρ", LocalMatrix(), state)));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "BoundCoherenceHigherDimensions", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "θ" => Theta,
        _ => F.Id(name)
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula NatCast(Formula value, Formula target) => Typed(At(Qualified("Nat", "cast"), value), target);
    private static Formula FinD() => At(Qualified("Fin"), X("d"));
    private static Formula ProductIndex() => Parenthesized(Seq(FinD(), Sp, Times, Sp, FinD()));
    private static Formula LocalMatrix() => At(Qualified("Matrix"), FinD(), FinD(), Complexes());
    private static Formula ProductMatrix() => At(Qualified("Matrix"), ProductIndex(), ProductIndex(), Complexes());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
