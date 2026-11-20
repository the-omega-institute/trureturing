using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class QuaternionModelAutomorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/QuaternionModelAutomorphism.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/LieTheory/cayley1855determinants");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maps from a ternary comparison structure into the unit quaternions that carry its transfer and reading to those of the quaternion comparison model are unique up to a left-right translation x -> p * x * q, and two such translations agree exactly when their pairs (p, q) agree up to a common sign.",
        H("Rigidity of the unit quaternion comparison model"),
        Blocks(
            Node("preserves-iff-exists-mul-mul", "preserves_iff_exists_mul_mul",
                "Transfer- and reading-preserving maps differ by a left-right translation",
                StatementSource.FromAuthor(RigidityFormula()), AssessedProvenance.FromRepo(), DescribeRole.Theorem,
                "Let C be a ternary comparison structure on M and u a map from M to the unit quaternions with u(tri(C, x, y, z)) = u(x) * u(y)^-1 * u(z) and kappa(C, x, y) = kappa(quaternionModel, u(x), u(y)), where the reading of the model is kappa(quaternionModel, p, q) = (1 + <p, q>) / 2 for the real inner product <p, q> of quaternions. "
                    + "The map u is injective, because a reading equal to one means equality both in C and in the unit quaternions, but it need not be onto, and no further hypothesis is placed on C. "
                    + "A second map v from M to the unit quaternions satisfies the same two identities if and only if there are unit quaternions p and q with v(x) = p * u(x) * q for every x. "
                    + "If v(x) = p * u(x) * q, the transfer is carried along because (p * a * q) * (p * b * q)^-1 * (p * c * q) = p * a * b^-1 * c * q, and the reading is carried along because a left-right translation preserves the reading of the model. "
                    + "Conversely, suppose that v carries the transfer and the reading. If M is empty there is nothing to prove; otherwise fix a point o of M and put a(x) = u(o)^-1 * u(x) and b(x) = v(o)^-1 * v(x). "
                    + "Left multiplication preserves the reading, so <b(x), b(y)> = <a(x), a(y)> for all x and y, and with y = o the families a and b have the same real parts. "
                    + "The transfer gives a(x) * a(y) = a(tri(C, x, o, y)) and b(x) * b(y) = b(tri(C, x, o, y)), so the product of two members of a is a member of a whose counterpart in b is the product of the two counterparts. "
                    + "Two families with these three properties are simultaneously conjugate: there are unit quaternions c and e with c * b(x) * c^-1 = e * a(x) * e^-1 for every x. "
                    + "If every a(x) is 1 or -1, then b = a. "
                    + "Otherwise some a(x0) is not real; unit quaternions with the same real part are conjugate, so a(x0) and b(x0) are both conjugate to a unit quaternion H of the plane spanned by 1 and i whose i coordinate is not zero. "
                    + "If every conjugated member of a lies in that plane, each commutes with H, so each corresponding member of b commutes with H and lies in the same plane; the real part and the inner product with H then determine it, and the conjugated families agree. "
                    + "If some conjugated member a(x1) lies outside that plane, a conjugation by a unit quaternion of the plane, which fixes H, moves a(x1) and b(x1) to one unit quaternion G of the space spanned by 1, i and j whose j coordinate is not zero; the inner products with 1, H, G and H * G determine every member, and again the conjugated families agree. "
                    + "Unwinding the normalization and the conjugations gives v(x) = p * u(x) * q with p = v(o) * c^-1 * e * u(o)^-1 and q = e^-1 * c. "
                    + "Neither identity required of v can be dropped. Take M to be the unit quaternions, C the quaternion comparison model and u the identity. "
                    + "The quaternion conjugation x -> x^-1 preserves the reading, because <x^-1, y^-1> = <x, y> for unit quaternions, but not the transfer: tri(quaternionModel, i, 1, j) = i * j = k is sent to -k, while the transfer of the images is (-i) * (-j) = k. "
                    + "The constant map with value 1 preserves the transfer but not the reading, since kappa(quaternionModel, 1, -1) = 0. "
                    + "By the theorem neither map has the form x -> p * x * q. "
                    + "With the same choice of M, C and u, the theorem says that the self-maps of the unit quaternions preserving the transfer and the reading of the model are exactly the maps x -> p * x * q. "
                    + "For a noncommutative, chain-connected structure of feature rank five whose reading touches zero and is complete, any two bijections onto the unit quaternions that carry the transfer and the reading therefore differ by such a map; if both send a point o to 1, then p * q = 1, and they differ by the conjugation x -> p * x * p^-1. This consequence, the theorem applied with p * q = 1, is not among the formal statements of the module. "
                    + "Every rotation of four-dimensional Euclidean space has the form x -> p * x * q with unit quaternions p and q, a classical description going back to Cayley; the theorem characterizes these maps on the unit sphere through the transfer and the reading alone, without assuming continuity or bijectivity."),
            Node("mul-mul-eq-mul-mul-iff", "mul_mul_eq_mul_mul_iff",
                "Two left-right translations agree exactly up to a common sign",
                StatementSource.FromAuthor(ParametrizationFormula()), AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                "In the formula the second pair (p', q') is written (r, s). "
                    + "For unit quaternions p, q, p' and q', the maps x -> p * x * q and x -> p' * x * q' of the unit quaternions agree if and only if (p', q') = (p, q) or (p', q') = (-p, -q). "
                    + "If the maps agree, x = 1 gives p * q = p' * q', so p' = p * t with t = q * q'^-1, and then p * x * q = p * t * x * q' for every unit quaternion x gives t * x = x * t. "
                    + "Commuting with i forces the j and k coordinates of t to vanish, and commuting with j forces its i coordinate to vanish, so t is a real unit quaternion, t = 1 or t = -1; this gives (p', q') = (p, q) or (p', q') = (-p, -q). "
                    + "Conversely (-p) * x * (-q) = p * x * q. "
                    + "Thus the map x -> p * x * q determines its pair (p, q) up to a common sign, and the parametrization of left-right translations by pairs of unit quaternions is two-to-one. "
                    + "This is the classical description of the kernel of the two-sided multiplication map (p, q) -> (x -> p * x * q) from pairs of unit quaternions onto the rotations of four-dimensional Euclidean space: the kernel is the subgroup {(1, 1), (-1, -1)}. "
                    + "The description of the rotations of four-dimensional space by pairs of quaternions is classically attributed to Cayley; the surjectivity onto the rotations is not among the formal statements of the module."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("quaternion-model-automorphism-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Iff(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula ExistsMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);

    private static Formula M => F.Id("M");
    private static Formula C => F.Id("C");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Quaternions => Seq(Mathbb, Grp(F.Id("H")), OpenBracket, Reals, CloseBracket);
    private static Formula Units => Call("unitary", Quaternions);
    private static Formula Model => Seq(Operatorname, Grp(F.Id("quaternionModel")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);

    /// <summary>The map f carries the transfer of C to the transfer of the model.</summary>
    private static Formula Transfer(Formula f)
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        return ForAllMany(M,
            Equal(At(f, Call("tri", C, x, y, z)), Call("tri", Model, At(f, x), At(f, y), At(f, z))),
            "x", "y", "z");
    }

    /// <summary>The reading of C equals the reading of the model on the images under f.</summary>
    private static Formula Reading(Formula f)
    {
        Formula x = F.Id("x"), y = F.Id("y");
        return ForAllMany(M,
            Equal(Call("kappa", C, x, y), Call("kappa", Model, At(f, x), At(f, y))), "x", "y");
    }

    private static Formula RigidityFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), x = F.Id("x"), p = F.Id("p"), q = F.Id("q");
        Formula maps = new Formula.TypeArrow(M, Units);
        Formula translation = ExistsMany(Units,
            ForAll("x", M, Equal(At(v, x), Mul(Mul(p, At(u, x)), q))), "p", "q");
        return Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M),
            ForAll("u", maps, Implies(Transfer(u), Implies(Reading(u),
                ForAll("v", maps, Iff(And(Transfer(v), Reading(v)), translation))))))));
    }

    private static Formula ParametrizationFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), r = F.Id("r"), s = F.Id("s"), x = F.Id("x");
        Formula agree = ForAll("x", Units, Equal(Mul(Mul(p, x), q), Mul(Mul(r, x), s)));
        Formula pairs = Or(And(Equal(r, p), Equal(s, q)), And(Equal(r, Neg(p)), Equal(s, Neg(q))));
        return Disp(ForAllMany(Units, Iff(agree, pairs), "p", "q", "r", "s"));
    }
}
