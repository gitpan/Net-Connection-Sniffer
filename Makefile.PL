use ExtUtils::MakeMaker;
use Config;
use lib qw(inc);
use Devel::CheckLib;
# check that 'pcap' lib is installed
check_lib_or_exit(
	lib	=> 'pcap',
);

my $pkg = 'Net::Connection::Sniffer';
$pkg =~ /[^:]+$/;
my $module = $& .'.pm';

# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile that is written.

my %makeparms = (
    'NAME'		=> $pkg,
    'VERSION_FROM'	=> $module, # finds $VERSION
    'PREREQ_PM'		=> {
				Net::DNS::Codes		=> 0.08,
				Net::DNS::ToolKit	=> 0.26,
				Net::Interface		=> 0.08,
				Net::NBsocket		=> 0.12,
				Sys::Hostname::FQDN	=> 0.07,
				Proc::PidUtil		=> 0.07,
				NetAddr::IP::Util	=> 0.11,
				Sys::Sig		=> 0.02,
			},
    'LIBS'		=> '-lpcap',
    'clean'		=> { FILES    => "*~ tmp*"},
    'dist'		=> {COMPRESS=>'gzip', SUFFIX=>'gz'}
);

sub MY::top_targets {
  package MY;
  my $inherited = shift->SUPER::top_targets(@_);
  $inherited =~ s/(pure_all\s+::.+)/$1 README/;
  $inherited;
}

sub MY::post_constants {
  my $post_constants = q|
MY_POD2TEXT = |. $Config{scriptdirexp} .'/pod2text' .q|   
|;
} 

sub MY::postamble {
  package MY;
  my $postamble = q|
README  : |. $module .q|
	@$(MY_POD2TEXT) |. $module .q| > README

|;
}

WriteMakefile(%makeparms);
