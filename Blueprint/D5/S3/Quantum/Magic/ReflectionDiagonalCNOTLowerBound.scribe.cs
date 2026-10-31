using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ReflectionDiagonalCNOTLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Computability/huangkosuginishimatsushita2024reflectiondiagonal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive even number of wires admits a reflection-symmetric diagonal unitary forcing the exponential CNOT lower bound.",
        H("The worst-case CNOT lower bound for reflection symmetry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gate"), DeclarationHandle.Create(Prefix + "gate"),
                H("Ancilla-free CNOT and real z rotations"),
                StatementSource.FromAuthor(Disp(GateFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A gate is either an ordered pair of distinct target and control wires, or a wire together with a real rotation angle. "
                    + "The two alternatives form a disjoint sum. All wire indices belong to Fin m, so there are no ancillary wires. "
                    + "This is the gate set in main_arXiv2.tex, lines 170 and 194; the absence of ancillas is also stated at line 1225."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gate-matrix"), DeclarationHandle.Create(Prefix + "gateMatrix"),
                H("The complex matrix of a gate"),
                StatementSource.FromAuthor(Disp(GateMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Qubits m denotes the Boolean functions on Fin m, as in D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.Qubits. "
                    + "Sum.elim selects the CNOT or rotation matrix from the gate's disjoint-sum tag. "
                    + "The CNOT matrix reindexes the columns of the identity by replacing the target bit with its exclusive-or with the control bit. "
                    + "Subtype.val explicitly extracts the ordered wire pair. The rotation matrix is diagonal: a false bit receives the exponential of minus half the angle times the imaginary unit, and a true bit receives the positive half-angle exponential. "
                    + "Complex.ofReal explicitly includes each real half-angle into the complex numbers. These are the CNOT and z-rotation gates used by the source's circuit model at lines 170 and 194."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circuit-matrix"), DeclarationHandle.Create(Prefix + "circuitMatrix"),
                H("The ordered product of gate matrices"),
                StatementSource.FromAuthor(Disp(CircuitMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The matrix of a finite circuit is the right fold of its gate matrices under multiplication, starting from the identity. "
                    + "Thus the first list entry is the leftmost matrix factor, and the empty circuit has the identity matrix. "
                    + "This expresses the finite circuits over the source's gate set, with realization up to a global phase as at lines 429–445."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cnot-count"), DeclarationHandle.Create(Prefix + "cnotCount"),
                H("Counting only CNOT gates"),
                StatementSource.FromAuthor(Disp(CnotCountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Filter the circuit with Sum.elim on its disjoint-sum tag and take the length of the retained list. "
                    + "The predicate is constantly true on CNOT pairs and constantly false on rotations; Function.const displays both constant branches. "
                    + "This is the CNOT gate count used at lines 229 and 434, independently of the number of rotations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("A hard reflection-symmetric phase function in every even dimension"),
                StatementSource.FromAuthor(Disp(Equal(Name("claim"), Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every positive natural n, there is a real phase function on twice n Boolean wires that is unchanged by complementing every bit. "
                    + "Every circuit whose matrix is a complex scalar multiple of its diagonal exponential has the stated natural-number CNOT lower bound. "
                    + "The scalar c is arbitrary in the statement; the matrix equality itself will force it to be nonzero. "
                    + "This gives the worst-case lower-bound reading of the conjecture at main_arXiv2.tex, line 847, for the symmetry defined at lines 207–227 and the global-phase convention at lines 429–445. "
                    + "The matching upper bound supplied by Algorithm 1 at lines 229 and 434 is separate from this assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The reflection-symmetric CNOT lower bound"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix n at least one and put m equal to twice n. Choose the phase to be pi divided by two at the all-false and all-true inputs and zero elsewhere. "
                        + "The two inputs are distinct because m is positive. Complementing every bit exchanges them and preserves the remaining inputs, so the phase has reflection symmetry. "
                        + "Its diagonal exponential is the imaginary unit at those two inputs and one elsewhere.")),
                    Paragraph(Text(
                        "Track a Boolean row vector on each wire, starting with the rows of the identity matrix. A CNOT replaces its target row by the sum of its target and control rows; a rotation leaves all rows unchanged. "
                        + "Boolean addition is exclusive-or. Evaluating the rows on an input commutes with a CNOT update. The corresponding bit toggle is an involution when target and control differ, so these updates preserve bijectivity of the linear map. "
                        + "An induction over the gate list expresses each matrix row as a nonzero product of rotation factors at the column selected by the final linear map, with all other entries zero. "
                        + "If the circuit matrix is diagonal, that selected column must be the original input. Equality of the linear maps on every input then makes the final row matrix the identity.")),
                    Paragraph(Text(
                        "For a Boolean vector v and a nowhere-zero complex function f, form a multiplicative invariant by multiplying f(x) when the Boolean dot product of v and x is false and multiplying its inverse when that dot product is true. "
                        + "The invariant is multiplicative in f. If a translation by u preserves f and has dot product true with v, pair each x with x plus u: the two exponents are opposite and their factors cancel. "
                        + "For nonzero v a coordinate vector supplies such a translation for every nonzero constant function, so a global scalar contributes one. "
                        + "For distinct nonzero vectors v and w, one coordinate vector or a sum of two coordinate vectors has dot product true with v and false with w. "
                        + "Consequently every nowhere-zero factor depending only on the dot product with w also contributes one.")),
                    Paragraph(Text(
                        "Induct over the circuit again. Bijectivity ensures that every current wire row is nonzero. If a fixed nonzero v never occurs on a rotated wire, the preceding cancellation applies to each rotation factor, and the invariant of their product is one. "
                        + "For an even Boolean vector v, however, its dot products with the all-false and all-true inputs are both false. On the chosen diagonal the invariant is therefore the product of two imaginary units, namely minus one; every other input contributes one. "
                        + "The diagonal equality and the final identity row matrix identify the product of rotation factors with c times this diagonal function. Nonvanishing at any input forces c to be nonzero. "
                        + "Multiplicativity and cancellation of c contradict the value one whenever a nonzero even v is absent. Thus every nonzero even vector occurs on a rotated wire.")),
                    Paragraph(Text(
                        "Remove the rotations from the list, retaining the ordered CNOT pairs. This preserves the final row matrix and makes the length of the remaining list equal to the CNOT count. "
                        + "Induction shows that a row used by a rotation is either an initial row or an earlier CNOT output. Every initial identity row is odd, so each required nonzero even vector must occur as a CNOT output. "
                        + "The final identity rows are odd as well. Apply D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting.count_bound to this list and the initial identity rows: "
                        + "the required even outputs number half of all Boolean vectors less one, and at least m minus one further updates are needed to restore odd rows. "
                        + "Substitution of m equal to twice n into that bound proves the assertion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("huang-kosugi-nishi-matsushita-2024-reflection-diagonal-cnot-lower-bound"),
                    ResolutionKind.Proved)))));

    private static Formula GateFormula() => All("m", Naturals(),
        Equal(Local("gate", X("m")), At(Qualified("Sum"), CnotPairs(X("m")), RotationPairs(X("m")))));

    private static Formula GateMatrixFormula()
    {
        Formula m = X("m");
        Formula pair = At(Qualified("Subtype", "val"), X("p"));
        Formula target = First(pair);
        Formula control = Second(pair);
        Formula toggle = LambdaOf("y", Qubits(m), At(Qualified("Function", "update"), X("y"), target,
            At(Qualified("Bool", "xor"), At(X("y"), target), At(X("y"), control))));
        Formula cnot = All("p", CnotPairs(m), Equal(Local("gateMatrix", At(Qualified("Sum", "inl"), X("p"))),
            At(Qualified("Matrix", "submatrix"), Typed(D(1), Operators(m)), Qualified("id"), toggle)));
        Formula phase = At(Qualified("Matrix", "diagonal"), LambdaOf("x", Qubits(m),
            If(Equal(At(X("x"), First(X("p"))), Qualified("Bool", "false")),
                Exponential(new Formula.Fraction(new Formula.Negate(Second(X("p"))), Typed(D(2), Reals()))),
                Exponential(new Formula.Fraction(Second(X("p")), Typed(D(2), Reals()))))));
        Formula rotation = All("p", RotationPairs(m), Equal(
            Local("gateMatrix", At(Qualified("Sum", "inr"), X("p"))), phase));
        return All("m", Naturals(), And(cnot, rotation));
    }

    private static Formula CircuitMatrixFormula() => All("m", Naturals(),
        All("circuit", ListOf(Local("gate", X("m"))), Equal(Local("circuitMatrix", X("circuit")),
            At(Qualified("List", "foldr"), LambdaOf("g", Local("gate", X("m")),
                LambdaOf("acc", Operators(X("m")), Mul(Local("gateMatrix", X("g")), X("acc")))),
                Typed(D(1), Operators(X("m"))), X("circuit")))));

    private static Formula CnotCountFormula()
    {
        Formula predicate = LambdaOf("g", Local("gate", X("m")), At(Qualified("Sum", "elim"),
            At(Qualified("Function", "const"), CnotPairs(X("m")), Qualified("Bool", "true")),
            At(Qualified("Function", "const"), RotationPairs(X("m")), Qualified("Bool", "false")), X("g")));
        return All("m", Naturals(), All("circuit", ListOf(Local("gate", X("m"))),
            Equal(Local("cnotCount", X("circuit")), At(Qualified("List", "length"),
                At(Qualified("List", "filter"), predicate, X("circuit"))))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = Mul(D(2), X("n"));
        Formula symmetric = All("x", Qubits(m), Equal(
            At(Theta, LambdaOf("j", Fin(m), At(Qualified("Bool", "not"), At(X("x"), X("j"))))),
            At(Theta, X("x"))));
        Formula diagonal = At(Qualified("Matrix", "diagonal"),
            LambdaOf("x", Qubits(m), Exponential(At(Theta, X("x")))));
        Formula bound = LE(Sub(Add(new Formula.Power(D(2), Sub(m, D(1))), m), D(2)),
            Local("cnotCount", X("circuit")));
        Formula realization = Equal(Local("circuitMatrix", X("circuit")),
            At(Qualified("HSMul", "hSMul"), X("c"), diagonal));
        return All("n", Naturals(), Imp(LE(D(1), X("n")), Ex(Theta, Arrow(Qubits(m), Reals()),
            And(symmetric, All("circuit", ListOf(Local("gate", m)), All("c", Complexes(), Imp(realization, bound)))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        Formula value = X(parts[0]);
        for (int i = 1; i < parts.Length; i++) value = Seq(value, Dot, X(parts[i]));
        return Seq(Operatorname, Grp(value));
    }
    private static Formula Name(string name) => Qualified(name);
    private static Formula Local(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Left, Open, value, Right, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula m) => At(Qualified("Fin"), m);
    private static Formula Qubits(Formula m) => At(Qualified("Qubits"), m);
    private static Formula ListOf(Formula type) => At(Qualified("List"), type);
    private static Formula Product(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Times, Sp, Parenthesized(right));
    private static Formula First(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Second(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula CnotPairs(Formula m) => At(Qualified("Subtype"), LambdaOf("p", Product(Fin(m), Fin(m)),
        NE(First(X("p")), Second(X("p")))));
    private static Formula RotationPairs(Formula m) => Product(Fin(m), Reals());
    private static Formula Operators(Formula m) => At(Qualified("Matrix"), Qubits(m), Qubits(m), Complexes());
    private static Formula Exponential(Formula angle) => At(Qualified("Complex", "exp"),
        Mul(At(Qualified("Complex", "ofReal"), Typed(angle, Reals())), Qualified("Complex", "I")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(string name, Formula domain, Formula body) => All(X(name), domain, body);
    private static Formula All(Formula variable, Formula domain, Formula body) => Seq(Forall, Sp, Typed(variable, domain), Comma, Sp, body);
    private static Formula Ex(Formula variable, Formula domain, Formula body) => Seq(Exists, Sp, Typed(variable, domain), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), domain), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
