class Circom < Formula
  desc "Circuit compiler for zkSNARK proving systems"
  homepage "https://github.com/IceColdCasino/circom"
  url "https://github.com/IceColdCasino/circom/archive/refs/tags/v2.2.5.tar.gz"
  sha256 "345334820616f028e263a171b5ec34d17f9bdda640b1ae2e3124245d2cfbda44"
  license "GPL-3.0-only"
  head "https://github.com/IceColdCasino/circom.git", branch: "master"

  depends_on "rust" => :build

  def install
    system "cargo", "install", *std_cargo_args(path: "circom")
  end

  test do
    assert_match "2.2.5", shell_output("#{bin}/circom --version")
  end
end
