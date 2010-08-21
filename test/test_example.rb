require File.dirname(__FILE__) + '/test_helper'

class TestExample < Test::Unit::TestCase
  def test_this
    assert_equal "Hello Dude!", Example.get_something
  end

end
