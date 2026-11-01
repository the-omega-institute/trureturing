using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostRelativeEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.";
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) =>
        new Formula.Apply(V(name), [.. args]);
    private static Formula A(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iffn(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Smul(Formula x, Formula y) => C("smul", x, y);
    private static Formula Cast(Formula x) => C("Int.cast", x);
    private static Formula K(Formula s) => C("ket", s);
    private static DocumentBlock Node(string name, Formula formula, string text,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create("relative-ghost-energy-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create()
    {
        var s = V("S"); var v = V("v"); var ell = V("ell");
        var sets = C("Finset", V("Nat")); var fock = V("Fock");
        var energy = C("energy", s); var relative = C("relativeEnergy", s);
        var noThree = A("S", sets, Imp(C("mem", D(3), s), Eqn(C("coeff", v, s), D(0))));
        var exactEnergy = A("S", sets, Imp(C("nonzero", C("coeff", v, s)),
            Eqn(relative, C("Int.ofNat", ell))));
        var groundLine = Exists("alpha", V("Complex"),
            Eqn(v, Smul(V("alpha"), K(C("singleton", D(1))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual ghost Virasoro zero mode supplies a finite relative-energy grading on the literal b0 kernel.",
            H("Relative energy on the original bc ghost carrier"), Blocks(
                Paragraph(Text("All operators act on the original CountableOccupationFock carrier. Site energy is -siteMode(j)*siteSign(j), occupation energy is its finite sum, and relativeEnergy(S)=energy(S)+1. Integer subtraction precedes scalar casting.")),
                Node("L_zero_ket", A("S", sets,
                    Eqn(C("L", D(0), K(s)), Smul(Cast(energy), K(s)))),
                    "Weight the statewise finite normal ordered summands by -q before reindexing the actual modeSite/siteMode bijection. The unweighted ghost-number identity is not used as a weighted identity."),
                Node("L_zero_coefficient", A("v", fock, A("S", sets,
                    Eqn(C("coeff", C("L", D(0), v), s), C("mul", Cast(energy), C("coeff", v, s))))),
                    "Linear extension of the actual zero-mode ket identity gives its coefficient action on every finite-excitation vector."),
                Node("b_zero_kernel_iff", A("v", fock,
                    Iffn(Eqn(C("b", D(0), v), D(0)), noThree)),
                    "The actual b0 is annihilation at site three. Its unique deletion preimage and nonzero phase give the literal kernel characterization, without a replacement representation."),
                Node("relative_level_coeff_iff", A("ell", V("Nat"), A("v", fock,
                    Iffn(C("RelativeLevel", ell, v), And(noThree, exactEnergy)))),
                    "RelativeLevel means b0(v)=0 and (L0+id)(v)=ell*v. Injectivity of integer casting into Complex recovers the exact integral occupation level."),
                Node("relative_ground_line", A("v", fock,
                    Iffn(And(C("RelativeKernel", v), Eqn(C("relativeOperator", v), D(0))),
                        groundLine)),
                    "The shift is fixed by the actual identity L0(c1 vacuum)=-c1 vacuum. Relative energy is the indicator of the missing site one plus strictly positive contributions from sites other than one and three. The literal b0 kernel excludes site three, leaving only the ground line."),
                Node("relative_level_support", A("ell", V("Nat"), A("v", fock,
                    Imp(C("RelativeLevel", ell, v), A("S", sets,
                        Imp(C("nonzero", C("coeff", v, s)), C("Finset.Subset", s,
                            C("Finset.range", Add(C("mul", D(2), ell), D(4))))))))),
                    "For an occupied even site 2k the energy is k+2; for an odd site 2k+1 it is k-1 in integers. Each nonexceptional occupied site's energy is bounded by the level, so every occupied site is below 2*ell+4."),
                Node("relativeLevelBasis", A("ell", V("Nat"),
                    C("Basis", C("levelOccupationSets", ell), V("Complex"), C("relativeLevelSpace", ell))),
                    "The index consists of occupations in the powerset of range(2*ell+4), excluding site three and with relativeEnergy ell. Coefficient evaluation proves independence and the original Finsupp expansion proves spanning; their basis lies in the actual relative level submodule.", DescribeRole.Definition),
                Node("relative_level_finite_dimensional", A("ell", V("Nat"),
                    C("FiniteDimensional", V("Complex"), C("relativeLevelSpace", ell))),
                    "The explicitly indexed finite ket basis derives finite dimensionality. It is not an assumed eigenbasis or a finite-dimensionality certificate."),
                Paragraph(Text("Signed negative-mode PBW, total BRST nilpotence, no-ghost, full string theory and AdS/CFT remain separate mathematical obligations.")))));
    }
}
